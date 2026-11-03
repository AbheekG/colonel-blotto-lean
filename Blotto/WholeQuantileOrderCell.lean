import Blotto.FinitePolytopeRationalWitness
import Blotto.RationalOrderCellCoefficients

/-! Actual arbitrary-law quantile anchors feed the constructed signed cell
and bounded rational vertex. The original joint probabilities need not be
uniform or rational. Every labelled tuple preserves its sum sign against
both budgets, and every originally feasible tuple remains feasible. This
closes the rational anchor/cell witness; constructing the transported whole
law and proving continuous-security equality/Farey comparator membership are
separate joins. No quantile, vertex or rationalization oracle is supplied. -/

namespace Blotto.WholeQuantileOrderCell
open MeasureTheory Set RationalOrderCell FinitePolytopeRationalWitness
open scoped BigOperators Classical

noncomputable def original {m : ℕ} (law : Mixed m) (K : ℕ) : Variable m K → ℝ :=
  fun v => DeterministicQuantileRounding.anchor (marginal law v.1) K
    ⟨v.2.val + 1,by have hl := v.2.isLt; omega⟩

theorem original_unit {m : ℕ} (law : Mixed m) (ownBudget : ℝ) (hBudget : ownBudget ≤ 1)
    (hLaw : Supported ownBudget law) (K : ℕ) (hK : 0 < K) :
    ∀ v, original law K v ∈ Icc (0 : ℝ) 1 := by
  intro v
  exact ⟨DeterministicQuantileRounding.anchor_nonnegative _
    (WholeQuantileRounding.marginal_unitSupported law ownBudget hBudget hLaw v.1) K hK _,
    DeterministicQuantileRounding.anchor_le_one _
      (WholeQuantileRounding.marginal_unitSupported law ownBudget hBudget hLaw v.1) K hK _⟩

theorem original_label {m : ℕ} (law : Mixed m) (K : ℕ) (field : Fin m) (label : Fin K) :
    refValue (original law K) (tupleReference field label) =
      DeterministicQuantileRounding.anchor (marginal law field) K label := by
  unfold tupleReference reference
  by_cases hZero : label.val = 0
  · simp [hZero,refValue,DeterministicQuantileRounding.anchor]
  · have hOne : label.val ≠ K := Nat.ne_of_lt label.isLt
    simp only [hZero,hOne,dite_false,refValue,original]
    congr 1
    apply Fin.ext
    change label.val - 1 + 1 = label.val
    omega

theorem original_tuple_sum {m : ℕ} (law : Mixed m) (K : ℕ) (labels : Fin m → Fin K) :
    tupleSum (original law K) labels = ∑ field, WholeQuantileRounding.labelledRow law K labels field := by
  unfold tupleSum WholeQuantileRounding.labelledRow
  exact Finset.sum_congr rfl (fun field _ => original_label law K field (labels field))

def rationalRef {m K : ℕ} (a : Variable m K → ℚ) : Reference m K → ℚ
  | none => 0
  | some none => 1
  | some (some v) => a v

theorem rationalRef_cast {m K : ℕ} (a : Variable m K → ℚ) (r : Reference m K) :
    (rationalRef a r : ℝ) = refValue (fun v => (a v : ℝ)) r := by
  cases r with
  | none => simp [rationalRef,refValue]
  | some r => cases r <;> simp [rationalRef,refValue]

def rationalRow {m K : ℕ} (coordinates : Coordinate m K → ℚ) (labels : Fin m → Fin K) : Fin m → ℚ :=
  fun field => rationalRef (fun v => coordinates (some v)) (tupleReference field (labels field))

theorem rationalRow_sum {m K : ℕ} (coordinates : Coordinate m K → ℚ) (labels : Fin m → Fin K) :
    (∑ field, (rationalRow coordinates labels field : ℝ)) =
      tupleSum (fun v => (coordinates (some v) : ℝ)) labels := by
  unfold rationalRow tupleSum
  exact Finset.sum_congr rfl (fun field _ => rationalRef_cast _ _)

theorem rationalRef_unit {m K : ℕ} (a : Variable m K → ℚ)
    (hUnit : ∀ v, (a v : ℝ) ∈ Icc (0 : ℝ) 1) (r : Reference m K) :
    (rationalRef a r : ℝ) ∈ Icc (0 : ℝ) 1 := by
  cases r with
  | none => norm_num [rationalRef]
  | some r => cases r with
    | none => norm_num [rationalRef]
    | some v => exact hUnit v

theorem rationalRef_denominator {m K : ℕ} (a : Variable m K → ℚ) (denominator : ℕ)
    (hDivides : ∀ v, (a v).den ∣ denominator) (r : Reference m K) :
    (rationalRef a r).den ∣ denominator := by
  cases r with
  | none => simp [rationalRef]
  | some r => cases r with
    | none => simp [rationalRef]
    | some v => exact hDivides v

theorem rationalRow_feasible_of_original {m K : ℕ} (budgets : Fin 2 → ℚ)
    (old : Variable m K → ℝ) (coordinates : Coordinate m K → ℚ)
    (hCell : FeasibleCell budgets old (fun coordinate => (coordinates coordinate : ℝ)))
    (hMargin : 0 < coordinates none) (labels : Fin m → Fin K) (budget : Fin 2)
    (hOld : tupleSum old labels ≤ (budgets budget : ℝ)) :
    Feasible (budgets budget : ℝ) (fun field => (rationalRow coordinates labels field : ℝ)) := by
  have hPositive : (0 : ℝ) < coordinates none := by exact_mod_cast hMargin
  have hSigns := all_tuple_budgets_preserved budgets old _ hCell hPositive labels budget
  refine ⟨?_,?_⟩
  · intro field
    exact (rationalRef_unit _ (fun v => feasible_unit budgets old _ hCell (some v))
      (tupleReference field (labels field))).1
  · rw [rationalRow_sum]
    rcases lt_or_eq_of_le hOld with hStrict | hEqual
    · exact (hSigns.1.mp hStrict).le
    · exact (hSigns.2.1.mp hEqual).le

/-- Actual arbitrary feasible whole-law anchors yield a finite rational
catalogue with the retained denominator envelope and every tuple-budget
comparison preserved. The catalogue can still contain unused infeasible rows. -/
theorem exists_rational_catalogue {m : ℕ} (law : Mixed m) (ownBudget : ℝ) (hBudget : ownBudget ≤ 1)
    (hLaw : Supported ownBudget law) (K : ℕ) (hK : 0 < K) (budgets : Fin 2 → ℚ) :
    ∃ coordinates : Coordinate m K → ℚ,
      FeasibleCell budgets (original law K) (fun coordinate => (coordinates coordinate : ℝ)) ∧
      0 < coordinates none ∧
      ∃ denominator : ℕ, 0 < denominator ∧
        denominator ≤ commonDenominator budgets * (m + 2) ^ (m * (K - 1) + 1) ∧
        (∀ field label, (rationalRow coordinates (fun _ => label) field).den ∣ denominator) ∧
        ∀ labels : Fin m → Fin K, ∀ budget : Fin 2,
          SameSign ((∑ field, WholeQuantileRounding.labelledRow law K labels field) - (budgets budget : ℝ))
            ((∑ field, (rationalRow coordinates labels field : ℝ)) - (budgets budget : ℝ)) := by
  obtain ⟨coordinates,hCell,hMargin,denominator,hDenPositive,hDenBound,hDivides⟩ :=
    order_cell_rational_witness budgets (original law K) (original_unit law ownBudget hBudget hLaw K hK)
  refine ⟨coordinates,hCell,hMargin,denominator,hDenPositive,hDenBound,?_,?_⟩
  · intro field label
    exact rationalRef_denominator _ denominator (fun v => hDivides (some v)) _
  · intro labels budget
    have hPositive : (0 : ℝ) < coordinates none := by exact_mod_cast hMargin
    have h := all_signs_preserved budgets (original law K) _ hCell hPositive (.inr (labels,budget))
    rw [rawRow_sum,rawRow_sum,original_tuple_sum,← rationalRow_sum] at h
    exact h

end Blotto.WholeQuantileOrderCell
