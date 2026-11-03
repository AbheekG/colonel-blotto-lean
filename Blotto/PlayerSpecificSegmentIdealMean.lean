import Blotto.PlayerSpecificOriginalResourceDiscrepancy

/-! Exact scalar semantics for sequential conditional segment choices.
The final fallback retains the remaining mass. Zero remaining mass uses
total division, matching the actual algebraic selector. -/
namespace Blotto.PlayerSpecificSegmentIdealMean
set_option autoImplicit false
set_option maxHeartbeats 2500000

def total {slots : ℕ} (weight : Fin slots → ℝ) (items : List (Fin slots)) : ℝ := (items.map weight).sum

def Remaining {slots : ℕ} (weight : Fin slots → ℝ) (items : List (Fin slots)) (mass : ℝ) : Prop :=
  (∀ slot ∈ items,0 ≤ weight slot) ∧ total weight items ≤ mass

theorem total_nonnegative {slots : ℕ} (weight : Fin slots → ℝ) (items : List (Fin slots))
    (h : ∀ slot ∈ items,0 ≤ weight slot) : 0 ≤ total weight items := by
  apply List.sum_nonneg
  intro w hw
  obtain ⟨slot,hs,rfl⟩ := List.mem_map.mp hw
  exact h slot hs

theorem head_bounds {slots : ℕ} (weight : Fin slots → ℝ) (slot : Fin slots) (rest : List (Fin slots)) (mass : ℝ)
    (h : Remaining weight (slot::rest) mass) :
    0 ≤ weight slot ∧ weight slot ≤ mass ∧ Remaining weight rest (mass-weight slot) := by
  have ht : ∀ j ∈ rest,0 ≤ weight j := fun j hj => h.1 j (List.mem_cons_of_mem slot hj)
  have hsum : weight slot+total weight rest ≤ mass := by
    simpa only [total,List.map_cons,List.sum_cons] using h.2
  have hp := total_nonnegative weight rest ht
  exact ⟨h.1 slot List.mem_cons_self,by linarith only [hsum,hp],ht,by linarith only [hsum]⟩

theorem probability_bounds {slots : ℕ} (weight : Fin slots → ℝ) (slot : Fin slots) (rest : List (Fin slots)) (mass : ℝ)
    (h : Remaining weight (slot::rest) mass) : 0 ≤ weight slot/mass ∧ weight slot/mass ≤ 1 := by
  have hb := head_bounds weight slot rest mass h
  have hm : 0 ≤ mass := hb.1.trans hb.2.1
  by_cases hz : mass=0
  · simp only [hz,div_zero,le_refl,zero_le_one,and_self]
  · have hp : 0 < mass := lt_of_le_of_ne hm (Ne.symm hz)
    exact ⟨div_nonneg hb.1 hm,(div_le_one hp).mpr hb.2.1⟩

noncomputable def mean {slots : ℕ} (weight : Fin slots → ℝ) (fallback : Fin slots) (f : Fin slots → ℝ) :
    List (Fin slots) → ℝ → ℝ
  | [],_ => f fallback
  | slot::rest,mass => weight slot/mass*f slot+(1-weight slot/mass)*mean weight fallback f rest (mass-weight slot)

theorem unit_bounds {slots : ℕ} (weight : Fin slots → ℝ) (fallback : Fin slots) (f : Fin slots → ℝ)
    (hf : ∀ j,0 ≤ f j ∧ f j ≤ 1) (items : List (Fin slots)) (mass : ℝ) (h : Remaining weight items mass) :
    0 ≤ mean weight fallback f items mass ∧ mean weight fallback f items mass ≤ 1 := by
  induction items generalizing mass with
  | nil => exact hf fallback
  | cons slot rest ih =>
    have hp := probability_bounds weight slot rest mass h
    have ht := ih _ (head_bounds weight slot rest mass h).2.2
    have hc : 0 ≤ 1-weight slot/mass := sub_nonneg.mpr hp.2
    rw [mean]
    constructor
    · exact add_nonneg (mul_nonneg hp.1 (hf slot).1) (mul_nonneg hc ht.1)
    · have hfirst := mul_le_mul_of_nonneg_left (hf slot).2 hp.1
      have hrest := mul_le_mul_of_nonneg_left ht.2 hc
      linarith only [hfirst,hrest]

theorem scaled_mean {slots : ℕ} (weight : Fin slots → ℝ) (fallback : Fin slots) (f : Fin slots → ℝ)
    (items : List (Fin slots)) (mass : ℝ) (h : Remaining weight items mass) :
    mass*mean weight fallback f items mass=(items.map (fun j => weight j*f j)).sum+
      (mass-total weight items)*f fallback := by
  induction items generalizing mass with
  | nil => simp only [mean,total,List.map_nil,List.sum_nil,sub_zero,zero_add]
  | cons slot rest ih =>
    have hb := head_bounds weight slot rest mass h
    have hc : mass*(weight slot/mass)=weight slot := by
      by_cases hz : mass=0
      · have hw : weight slot=0 := le_antisymm (hb.2.1.trans_eq hz) hb.1
        simp only [hz,hw,div_zero,mul_zero]
      · field_simp
    calc
      _ = (mass*(weight slot/mass))*f slot+(mass-mass*(weight slot/mass))*mean weight fallback f rest (mass-weight slot) := by rw [mean]; ring
      _ = weight slot*f slot+(mass-weight slot)*mean weight fallback f rest (mass-weight slot) := by rw [hc]
      _ = weight slot*f slot+((rest.map (fun j => weight j*f j)).sum+((mass-weight slot)-total weight rest)*f fallback) := by rw [ih _ hb.2.2]
      _ = _ := by simp only [total,List.map_cons,List.sum_cons]; ring

theorem normalized_mean {slots : ℕ} (weight : Fin slots → ℝ) (fallback : Fin slots) (f : Fin slots → ℝ)
    (items : List (Fin slots)) (h : Remaining weight items 1) :
    mean weight fallback f items 1=(items.map (fun j => weight j*f j)).sum+(1-total weight items)*f fallback := by
  simpa only [one_mul] using scaled_mean weight fallback f items 1 h

end Blotto.PlayerSpecificSegmentIdealMean
