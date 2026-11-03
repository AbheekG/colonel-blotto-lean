import Blotto.RationalWholeRowPayoff
import Blotto.ContinuousSecurityValues

/-! Whole-row dictionaries for the selected general-paper algorithm.
Labels retain row identity; repeated anchors are distinct labels. Balanced
label masses are an explicit quantizer obligation, not independent fields.
This module proves the semantic transfer ingredients, not a quantizer cost.
-/
namespace Blotto.GeneralPaperDictionary
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

structure Dictionary (T m K : ℕ) where
  label : Fin T → Fin m → Fin K
  anchor : Fin m → Fin K → ℚ

def law {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) : RationalWholeRowLaw T m where
  weight := fun _ => 1/(T:ℚ)
  nonnegative := fun _ => by positivity
  sum_one := by
    simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul]
    have h : (T:ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
    field_simp
  row := fun i j => d.anchor j (d.label i j)

noncomputable def labelMass {T m K : ℕ} (d : Dictionary T m K) (j : Fin m) (l : Fin K) : ℝ :=
  ∑ i, if d.label i j=l then 1/(T:ℝ) else 0

def Balanced {T m K : ℕ} (d : Dictionary T m K) : Prop :=
  ∀ j l, labelMass d j l=1/(K:ℝ)

theorem regroup {T m K : ℕ} (d : Dictionary T m K) (j : Fin m) (f : Fin K → ℝ) :
    (∑ i, (1/(T:ℝ))*f (d.label i j))=∑ l, labelMass d j l*f l := by
  symm
  unfold labelMass
  simp_rw [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem average_labels {T m K : ℕ} (d : Dictionary T m K) (h : Balanced d)
    (j : Fin m) (f : Fin K → ℝ) :
    (∑ i, (1/(T:ℝ))*f (d.label i j))=(1/(K:ℝ))*∑ l,f l := by
  rw [regroup]
  simp_rw [h j]
  exact (Finset.mul_sum _ _ _).symm

theorem payoff_formula {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (h : Balanced d)
    (v : Values m) (y : Allocation m) :
    purePayoff v y (law d hT).law =
      ∑ j,v.weight j*((1/(K:ℝ))*∑ l,share (y j) (d.anchor j l:ℝ)) := by
  have hw (i : Fin T) : (law d hT).realWeight i=1/(T:ℝ) := by
    simp only [law,RationalWholeRowLaw.realWeight,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  have hr (i : Fin T) (j : Fin m) : (law d hT).realRow i j=(d.anchor j (d.label i j):ℝ) := rfl
  rw [RationalWholeRowLaw.purePayoff_eq_sum]
  simp only [payoff,hw,hr]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = v.weight j * ∑ i,(1/(T:ℝ))*share (y j) (d.anchor j (d.label i j):ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [average_labels d h j (fun l => share (y j) (d.anchor j l:ℝ))]
      simp only [Finset.mul_sum,mul_assoc]

noncomputable def prefixPayoff {m K : ℕ} (v : Values m) (l : Fin m → Fin K) : ℝ :=
  ∑ j,v.weight j*((l j).val+1)/(K:ℝ)

theorem share_prefix_lower {K : ℕ} (a : Fin K → ℚ) (hOrder : Monotone a)
    (l : Fin K) (y : ℝ) (hy : (a l:ℝ)<y) :
    (l.val+1:ℝ) ≤ ∑ r,share y (a r:ℝ) := by
  calc
    _ = ∑ r ∈ Finset.Iic l,(1:ℝ) := by simp [Fin.card_Iic]
    _ = ∑ r ∈ Finset.Iic l,share y (a r:ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      have ha : (a r:ℝ) ≤ (a l:ℝ) := by exact_mod_cast hOrder (Finset.mem_Iic.mp hr)
      simp only [share,ite_eq_left (ha.trans_lt hy)]
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => share_nonneg _ _)

theorem share_prefix_upper {K : ℕ} (a : Fin K → ℚ) (l : Fin K) (y : ℝ)
    (hAffordable : ∀ r,(a r:ℝ) ≤ y ↔ r ≤ l) :
    (∑ r,share y (a r:ℝ)) ≤ (l.val+1:ℝ) := by
  calc
    _ ≤ ∑ r,if r ≤ l then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro r _
      by_cases hr : r ≤ l
      · simp only [ite_eq_left hr]
        exact share_le_one _ _
      · simp only [ite_eq_right hr]
        have hy : y<(a r:ℝ) := lt_of_not_ge (fun h => hr ((hAffordable r).mp h))
        simp [share,not_lt_of_ge hy.le,ne_of_lt hy]
    _ = _ := by simp [← Finset.mem_Iic,Fin.card_Iic]

theorem prefix_lower {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (h : Balanced d)
    (v : Values m) (hOrder : ∀ j,Monotone (d.anchor j)) (l : Fin m → Fin K)
    (y : Allocation m) (hy : ∀ j,(d.anchor j (l j):ℝ)<y j) :
    prefixPayoff v l ≤ purePayoff v y (law d hT).law := by
  rw [payoff_formula d hT h]
  unfold prefixPayoff
  apply Finset.sum_le_sum
  intro j _
  have h1 := mul_le_mul_of_nonneg_left (share_prefix_lower (d.anchor j) (hOrder j) (l j) (y j) (hy j))
    (show 0 ≤ 1/(K:ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left h1 (v.positive j).le
  convert h2 using 1 <;> ring

theorem prefix_upper {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (h : Balanced d)
    (v : Values m) (l : Fin m → Fin K) (y : Allocation m)
    (hAffordable : ∀ j r,(d.anchor j r:ℝ) ≤ y j ↔ r ≤ l j) :
    purePayoff v y (law d hT).law ≤ prefixPayoff v l := by
  rw [payoff_formula d hT h]
  unfold prefixPayoff
  apply Finset.sum_le_sum
  intro j _
  have h1 := mul_le_mul_of_nonneg_left (share_prefix_upper (d.anchor j) (l j) (y j) (hAffordable j))
    (show 0 ≤ 1/(K:ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left h1 (v.positive j).le
  convert h2 using 1 <;> ring

noncomputable def cost {T m K : ℕ} (d : Dictionary T m K) (l : Fin m → Fin K) : ℝ :=
  ∑ j,(d.anchor j (l j):ℝ)

theorem strict_overbid_exists {T m K : ℕ} (d : Dictionary T m K) (l : Fin m → Fin K)
    (hNonnegative : ∀ j r,0 ≤ d.anchor j r) (budget : ℝ) (hCost : cost d l<budget) :
    ∃ y : Allocation m,Feasible budget y ∧ ∀ j,(d.anchor j (l j):ℝ)<y j := by
  let delta := (budget-cost d l)/((m:ℝ)+1)
  have hDen : 0<(m:ℝ)+1 := by positivity
  have hDelta : 0<delta := div_pos (sub_pos.mpr hCost) hDen
  have hProduct : ((m:ℝ)+1)*delta=budget-cost d l := by
    dsimp only [delta]
    field_simp
  refine ⟨fun j => (d.anchor j (l j):ℝ)+delta,⟨?_,?_⟩,?_⟩
  · intro j
    have ha : (0:ℝ) ≤ d.anchor j (l j) := by exact_mod_cast hNonnegative j (l j)
    linarith
  · simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_fin,nsmul_eq_mul]
    change cost d l+(m:ℝ)*delta ≤ budget
    nlinarith only [hProduct,hDelta]
  · intro j
    linarith

theorem strict_tuple_lower_bound {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (h : Balanced d)
    (v : Values m) (hOrder : ∀ j,Monotone (d.anchor j)) (hNonnegative : ∀ j r,0 ≤ d.anchor j r)
    (budget : ℝ) (l : Fin m → Fin K) (hCost : cost d l<budget) :
    prefixPayoff v l ≤ security v budget (law d hT).law := by
  obtain ⟨y,hy,hAbove⟩ := strict_overbid_exists d l hNonnegative budget hCost
  exact (prefix_lower d hT h v hOrder l y hAbove).trans (purePayoff_le_security v hy _)

theorem balanced_of_counts {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (hK : 0<K)
    (hCounts : ∀ j l,(Finset.univ.filter (fun i => d.label i j=l)).card*K=T) : Balanced d := by
  intro j l
  have ht : (0:ℝ)<T := by exact_mod_cast hT
  have hk : (0:ℝ)<K := by exact_mod_cast hK
  have hc : ((Finset.univ.filter (fun i => d.label i j=l)).card:ℝ)*(K:ℝ)=T := by
    exact_mod_cast hCounts j l
  have hm : labelMass d j l=((Finset.univ.filter (fun i => d.label i j=l)).card:ℝ)/(T:ℝ) := by
    simp only [labelMass,Finset.sum_ite,Finset.sum_const,Finset.sum_const_zero,
      add_zero,nsmul_eq_mul]
    ring
  rw [hm]
  apply (div_eq_div_iff (ne_of_gt ht) (ne_of_gt hk)).mpr
  nlinarith only [hc]

theorem law_supported {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (budget : ℝ)
    (hNonnegative : ∀ j l,0 ≤ d.anchor j l) (hRows : ∀ i,∑ j,(d.anchor j (d.label i j):ℝ) ≤ budget) :
    Supported budget (law d hT).law := by
  apply RationalWholeRowLaw.law_supported
  intro i
  refine ⟨?_,hRows i⟩
  intro j
  change (0:ℝ) ≤ d.anchor j (d.label i j)
  exact_mod_cast hNonnegative j (d.label i j)

end Blotto.GeneralPaperDictionary
