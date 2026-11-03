import Blotto.PlayerSpecificFiniteParameterContract

/-! Additive height growth in the actual rational sweep. Every move adds
or subtracts one fresh original field term; it does not multiply two
growing accumulators or incur exponential precision growth. -/
namespace Blotto.PlayerSpecificRationalSweepHeights
open PlayerSpecificCubic PlayerSpecificSweep PlayerSpecificSweepBounds PlayerSpecificPolynomialHeights
set_option autoImplicit false
set_option maxHeartbeats 2500000

def FieldsHeight (fields : List (ℚ×ℚ)) (H : ℕ) : Prop :=
  ∀ x∈fields,RationalHeight x.1 H ∧ RationalHeight x.2 H
def StateHeight (s : State ℚ) (H : ℕ) : Prop :=
  RationalHeight s.coefficients.A1 H ∧ RationalHeight s.coefficients.A2 H ∧
  RationalHeight s.coefficients.B1 H ∧ RationalHeight s.coefficients.B2 H ∧ RationalHeight s.prefixMax H
def initialBound (N H : ℕ) : ℕ := (3*H+1)*(N+1)+1
def stepBound (T H : ℕ) : ℕ := T+3*H+1

theorem max_height (a b : ℚ) (H : ℕ) (ha : RationalHeight a H) (hb : RationalHeight b H) : RationalHeight (max a b) H := by
  rcases le_total a b with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

theorem state_mono (s : State ℚ) (H J : ℕ) (h : StateHeight s H) (hHJ : H≤J) : StateHeight s J :=
  ⟨h.1.mono hHJ,h.2.1.mono hHJ,h.2.2.1.mono hHJ,h.2.2.2.1.mono hHJ,h.2.2.2.2.mono hHJ⟩

theorem square_divide (v w : ℚ) (H : ℕ) (hv : RationalHeight v H) (hw : RationalHeight w H) :
    RationalHeight (v^2/w) (3*H) := by
  have h:=(hv.mul hv).div hw
  simpa only [pow_two,show H+H+H=3*H by omega] using h

theorem initial_height (fields : List (ℚ×ℚ)) (H : ℕ) (hh : FieldsHeight fields H) (_hH : 1≤H) :
    StateHeight (initial fields) (initialBound fields.length H) := by
  have hsum:=RationalHeight.list_sum (l := fields.map Prod.snd) (s := H) (by
    intro q hq
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hq
    exact (hh x hx).2)
  have hterms:=RationalHeight.list_sum (l := fields.map (fun x => x.2^2/x.1)) (s := 3*H) (by
    intro q hq
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hq
    exact square_divide x.2 x.1 H (hh x hx).2 (hh x hx).1)
  simp only [List.length_map] at hsum hterms
  have hlarge : 1 ≤ initialBound fields.length H := by unfold initialBound; omega
  have hleft : (H+1)*fields.length+1 ≤ initialBound fields.length H := by unfold initialBound; nlinarith
  have hright : (3*H+1)*fields.length+1 ≤ initialBound fields.length H := by unfold initialBound; nlinarith
  exact ⟨hsum.mono hleft,zero_height.mono hlarge,hterms.mono hright,zero_height.mono hlarge,zero_height.mono hlarge⟩

theorem move_height (s : State ℚ) (v w : ℚ) (T H : ℕ) (hs : StateHeight s T)
    (hv : RationalHeight v H) (hw : RationalHeight w H) : StateHeight (move s v w) (stepBound T H) := by
  have hA2:=square_divide v w H hv hw
  have hB1:=square_divide w v H hw hv
  have hsmall : T+H+1≤stepBound T H := by unfold stepBound; omega
  have hT : T≤stepBound T H := by unfold stepBound; omega
  have hH : H≤stepBound T H := by unfold stepBound; omega
  exact ⟨(hs.1.sub hw).mono hsmall,hs.2.1.add hA2,hs.2.2.1.sub hB1,
    (hs.2.2.2.1.add hv).mono hsmall,max_height s.prefixMax v _ (hs.2.2.2.2.mono hT) (hv.mono hH)⟩

theorem maximum_height (fields : List (ℚ×ℚ)) (H : ℕ) (hh : FieldsHeight fields H) (hH : 1≤H) :
    RationalHeight (maximum Prod.snd fields) H := by
  induction fields with
  | nil => exact zero_height.mono hH
  | cons x xs ih =>
    exact max_height x.2 _ H (hh x List.mem_cons_self).2
      (ih (fun y hy => hh y (List.mem_cons_of_mem x hy)))

theorem suffix_height (fields : List (ℚ×ℚ)) (H : ℕ) (hh : FieldsHeight fields H) (hH : 1≤H) :
    ∀ x∈(suffixes fields).2.1,RationalHeight x.1.1 H ∧ RationalHeight x.1.2 H ∧ RationalHeight x.2 H := by
  induction fields with
  | nil => intro x hx; cases hx
  | cons x xs ih =>
    rw [suffixes_cons]
    intro y hy
    rcases List.mem_cons.mp hy with he | ht
    · subst y
      exact ⟨(hh x List.mem_cons_self).1,(hh x List.mem_cons_self).2,maximum_height (x::xs) H hh hH⟩
    · exact ih (fun z hz => hh z (List.mem_cons_of_mem x hz)) y ht

end Blotto.PlayerSpecificRationalSweepHeights
