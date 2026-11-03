import Blotto.GeneralPaperTaggedNativeOptimizer
import Blotto.FareyResponseSlack

/-! The paper's physical shift, with factor four and the shared proxy
numerator/denominator cap, realizes exactly its symbolic response budget
predicate. The nonzero threshold gap is derived from bounded denominators;
no slack or physical-budget oracle is supplied. Alphabet/catalogue generation
must still provide those actual bounded closed thresholds.
-/
namespace Blotto.GeneralPaperTagBudgetTransfer
open scoped BigOperators
open GeneralPaperResponseTag GeneralPaperResponseTagSums
set_option autoImplicit false
set_option maxHeartbeats 3500000

def shiftDenominator (m qbar C : ℕ) : ℕ := 4*m*qbar*C^(m+2)

def shift (m qbar C : ℕ) : ℚ := 1/(shiftDenominator m qbar C:ℚ)

theorem shift_positive (m qbar C : ℕ) (hm : 0<m) (hQ : 0<qbar) (hC : 0<C) : 0<shift m qbar C := by
  unfold shift shiftDenominator
  positivity

theorem denominator_gt_gap_scale (m q qbar C : ℕ) (hm : 0<m) (hq : 0<q) (hCap : q≤qbar) (hC : 0<C) :
    m*q*C^m<shiftDenominator m qbar C := by
  have hQbar : 0<qbar := by omega
  have hp : C^m≤C^(m+2) := pow_le_pow_right₀ (by omega : 1≤C) (by omega)
  have ha := Nat.mul_le_mul_right (C^m) (Nat.mul_le_mul_left m hCap)
  have hb := Nat.mul_le_mul_left (m*qbar) hp
  have hc : 0<m*qbar*C^(m+2) := by positivity
  have hd : shiftDenominator m qbar C=4*(m*qbar*C^(m+2)) := by unfold shiftDenominator; ring
  rw [hd]
  omega

theorem aggregate_lt_slack (m q qbar C : ℕ) (hm : 0<m) (hq : 0<q) (hCap : q≤qbar) (hC : 0<C)
    (B : ℚ) (hBudgetDen : B.den∣q) (threshold : Fin m → Farey.Fraction)
    (hDen : ∀ j, (threshold j).den≤C) (hSlack : (∑ j, (threshold j).value)<B) :
    (m:ℚ)*shift m qbar C<B-∑ j, (threshold j).value := by
  have hQbar : 0<qbar := by omega
  have hd : (0:ℚ)<shiftDenominator m qbar C := by unfold shiftDenominator; positivity
  have hs : (0:ℚ)<(q:ℚ)*(C:ℚ)^m := by positivity
  have hSmall : (m:ℚ)*shift m qbar C<1/((q:ℚ)*(C:ℚ)^m) := by
    rw [shift,mul_one_div]
    apply (div_lt_div_iff₀ hd hs).mpr
    have hc := denominator_gt_gap_scale m q qbar C hm hq hCap hC
    have he : (m:ℚ)*(q:ℚ)*(C:ℚ)^m<(shiftDenominator m qbar C:ℚ) := by exact_mod_cast hc
    simpa only [one_mul,mul_assoc] using he
  exact hSmall.trans_le (Farey.threshold_gap_lower_bound m q C hq B hBudgetDen threshold hDen hSlack)

def rowTag {m : ℕ} (threshold : Fin m → Farey.Fraction) (opened : Fin m → Bool) : Tag :=
  (List.ofFn (fun j => (⟨(threshold j).value,opened j⟩:Tag))).sum

theorem threshold_total {m : ℕ} (threshold : Fin m → Farey.Fraction) (opened : Fin m → Bool) :
    (rowTag threshold opened).threshold=∑ j, (threshold j).value := by
  rw [rowTag,threshold_sum]
  simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn]

theorem closed_total {m : ℕ} (threshold : Fin m → Farey.Fraction) (opened : Fin m → Bool) :
    (rowTag threshold opened).opened=false ↔ ∀ j, opened j=false := by
  rw [rowTag,sum_closed_iff]
  constructor
  · intro h j
    exact h _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
  · intro h a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact h j

theorem tag_budget_iff {m : ℕ} (threshold : Fin m → Farey.Fraction) (opened : Fin m → Bool) (B : ℚ) :
    rowTag threshold opened≤budget B ↔
      (∑ j, (threshold j).value)<B ∨ ((∑ j, (threshold j).value)=B ∧ ∀ j, opened j=false) := by
  rw [feasible_iff,threshold_total,closed_total]

def physical {m : ℕ} (threshold : Fin m → Farey.Fraction) (opened : Fin m → Bool) (delta : ℚ) : ℚ :=
  ∑ j, ((threshold j).value+if opened j then delta else 0)

theorem physical_lower {m : ℕ} (threshold : Fin m → Farey.Fraction) (opened : Fin m → Bool) (delta : ℚ) (hDelta : 0≤delta) :
    (∑ j, (threshold j).value)≤physical threshold opened delta := by
  apply Finset.sum_le_sum
  intro j _
  apply le_add_of_nonneg_right
  cases opened j <;> simp [hDelta]

theorem physical_upper {m : ℕ} (threshold : Fin m → Farey.Fraction) (opened : Fin m → Bool) (delta : ℚ) (hDelta : 0≤delta) :
    physical threshold opened delta≤(∑ j, (threshold j).value)+(m:ℚ)*delta := by
  have hb : (∑ j : Fin m, if opened j then delta else 0)≤(m:ℚ)*delta := by
    calc
      _ ≤ ∑ _j : Fin m, delta := by
        apply Finset.sum_le_sum
        intro j _
        cases opened j <;> simp [hDelta]
      _ = _ := by simp
  rw [physical,Finset.sum_add_distrib]
  exact add_le_add le_rfl hb

theorem physical_closed {m : ℕ} (threshold : Fin m → Farey.Fraction) (opened : Fin m → Bool) (delta : ℚ)
    (hClosed : ∀ j, opened j=false) : physical threshold opened delta=∑ j, (threshold j).value := by
  simp only [physical,hClosed,Bool.false_eq_true,ite_false,add_zero]

theorem physical_open_strict {m : ℕ} (threshold : Fin m → Farey.Fraction) (opened : Fin m → Bool) (delta : ℚ)
    (hDelta : 0<delta) (j : Fin m) (hOpen : opened j=true) : (∑ j, (threshold j).value)<physical threshold opened delta := by
  have hBump : delta≤∑ i : Fin m, if opened i then delta else 0 := by
    have he := Finset.single_le_sum (f := fun i : Fin m => if opened i then delta else 0)
      (fun i _ => by cases opened i <;> simp [hDelta.le]) (Finset.mem_univ j)
    simpa only [hOpen,ite_true] using he
  rw [physical,Finset.sum_add_distrib]
  linarith only [hDelta,hBump]

theorem physical_budget_iff (m q qbar C : ℕ) (hm : 0<m) (hq : 0<q) (hCap : q≤qbar) (hC : 0<C)
    (B : ℚ) (hBudgetDen : B.den∣q) (threshold : Fin m → Farey.Fraction)
    (hDen : ∀ j, (threshold j).den≤C) (opened : Fin m → Bool) :
    physical threshold opened (shift m qbar C)≤B ↔ rowTag threshold opened≤budget B := by
  have hShift := shift_positive m qbar C hm (by omega) hC
  rw [tag_budget_iff]
  constructor
  · intro hPhysical
    have hLower := (physical_lower threshold opened _ hShift.le).trans hPhysical
    by_cases hStrict : (∑ j, (threshold j).value)<B
    · exact Or.inl hStrict
    · have hEq : (∑ j, (threshold j).value)=B := le_antisymm hLower (le_of_not_gt hStrict)
      right
      refine ⟨hEq,?_⟩
      intro j
      cases hOpen : opened j
      · rfl
      · have he := physical_open_strict threshold opened _ hShift j hOpen
        linarith only [he,hPhysical,hEq]
  · rintro (hStrict|⟨hEq,hClosed⟩)
    · have hGap := aggregate_lt_slack m q qbar C hm hq hCap hC B hBudgetDen threshold hDen hStrict
      have hUpper := physical_upper threshold opened _ hShift.le
      linarith only [hGap,hUpper]
    · rw [physical_closed threshold opened _ hClosed,hEq]

end Blotto.GeneralPaperTagBudgetTransfer
