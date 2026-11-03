import Blotto.WholeQuantileRationalTransport
import Blotto.FiniteAnchorSecurityTransport

/-! The actual signed-cell catalogue feeds the exact two-way response
transport. Rationalization therefore preserves the continuous security of
the already-rounded whole law. Original real label probabilities and joint
dependence are retained; this is not a rational-weight mixture assertion. -/

namespace Blotto.WholeQuantileRationalSecurity
open MeasureTheory Set RationalOrderCell WholeQuantileOrderCell WholeQuantileRationalTransport
open scoped BigOperators Classical

theorem catalogue {m K : ℕ} (law : Mixed m) (hK : 0 < K)
    (budgets : Fin 2 → ℚ) (coordinates : Coordinate m K → ℚ)
    (hCell : FeasibleCell budgets (original law K) (fun coordinate => (coordinates coordinate : ℝ)))
    (hMargin : 0 < coordinates none) (budget : Fin 2) :
    FiniteAnchorResponseTransport.Catalogue (oldAnchor law K) (newAnchor coordinates) (budgets budget : ℝ) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro field
    refine ⟨⟨0,hK⟩,?_,?_⟩
    · simp [oldAnchor,DeterministicQuantileRounding.anchor]
    · simp [newAnchor,rationalRow,rationalRef,tupleReference,reference]
  · intro field label
    exact (rationalRef_unit _ (fun v => feasible_unit budgets (original law K) _ hCell (some v)) _).1
  · intro field left right
    exact (label_orders law budgets coordinates hCell hMargin field left right).1
  · intro field left right
    exact (label_orders law budgets coordinates hCell hMargin field left right).2
  · intro labels
    have hp : (0 : ℝ) < coordinates none := by exact_mod_cast hMargin
    have h := all_tuple_budgets_preserved budgets (original law K) _ hCell hp labels budget
    rw [original_tuple_sum,← rationalRow_sum] at h
    exact h.1
  · intro labels
    have hp : (0 : ℝ) < coordinates none := by exact_mod_cast hMargin
    have h := all_tuple_budgets_preserved budgets (original law K) _ hCell hp labels budget
    rw [original_tuple_sum,← rationalRow_sum] at h
    exact h.2.1

/-- Rationalization preserves the EXACT supremum over all at-most-budget
continuous responses, rather than a finite-grid or closed-only response set. -/
theorem transportedLaw_security {m K : ℕ} (values : Values m) (law : Mixed m)
    (ownBudget : ℝ) (hBudget : ownBudget ≤ 1) (hLaw : Supported ownBudget law) (hK : 0 < K)
    (budgets : Fin 2 → ℚ) (coordinates : Coordinate m K → ℚ)
    (hCell : FeasibleCell budgets (original law K) (fun coordinate => (coordinates coordinate : ℝ)))
    (hMargin : 0 < coordinates none) (budget : Fin 2) :
    security values (budgets budget : ℝ) (transportedLaw law hK coordinates) =
      security values (budgets budget : ℝ) (WholeQuantileRounding.roundedLaw law K hK) := by
  rw [transportedLaw_rounding law ownBudget hBudget hLaw hK coordinates]
  apply FiniteAnchorSecurityTransport.security_map_eq values (oldAnchor law K) (newAnchor coordinates)
    (budgets budget : ℝ) (catalogue law hK budgets coordinates hCell hMargin budget)
  · intro field label
    exact DeterministicQuantileRounding.anchor_nonnegative _
      (WholeQuantileRounding.marginal_unitSupported law ownBudget hBudget hLaw field) K hK label
  · exact (WholeQuantileRounding.roundedLaw_finite_supported law ownBudget hBudget hLaw K hK).mono fun row hr => by
      obtain ⟨labels,_,he⟩ := Finset.mem_image.mp hr.1
      exact ⟨labels,he.symm⟩

/-- An arbitrary feasible law has an ACTUAL whole-law rational comparator
with at most K^m rows and one bounded common anchor denominator. Every
continuous-response security increases by at most 1/K. Weights can be real. -/
theorem exists_rational_comparator {m : ℕ} (values : Values m) (law : Mixed m)
    (budgets : Fin 2 → ℚ) (own opposing : Fin 2)
    (hOwn : (budgets own : ℝ) ≤ 1) (hLaw : Supported (budgets own : ℝ) law)
    (hOpposing : 0 ≤ (budgets opposing : ℝ)) (K : ℕ) (hK : 0 < K) :
    ∃ coordinates : Coordinate m K → ℚ, ∃ denominator : ℕ,
      0 < denominator ∧
      denominator ≤ commonDenominator budgets * (m + 2) ^ (m * (K - 1) + 1) ∧
      (∀ field label, (rationalRow coordinates (fun _ => label) field).den ∣ denominator) ∧
      Supported (budgets own : ℝ) (transportedLaw law hK coordinates) ∧
      (rationalRows coordinates).card ≤ K ^ m ∧
      (∀ᵐ row ∂(transportedLaw law hK coordinates : Measure (Allocation m)),
        row ∈ (rationalRows coordinates : Set (Allocation m))) ∧
      security values (budgets opposing : ℝ) (transportedLaw law hK coordinates) ≤
        security values (budgets opposing : ℝ) law + 1 / K := by
  obtain ⟨coordinates,hCell,hMargin,denominator,hPositive,hBound,hDivides,_⟩ :=
    exists_rational_catalogue law (budgets own : ℝ) hOwn hLaw K hK budgets
  refine ⟨coordinates,denominator,hPositive,hBound,hDivides,
    transportedLaw_supported law hK budgets coordinates hCell hMargin own hOwn hLaw,
    rationalRows_card coordinates,
    transportedLaw_finite_supported law hK budgets coordinates hCell hMargin _ hOwn hLaw,?_⟩
  rw [transportedLaw_security values law _ hOwn hLaw hK budgets coordinates hCell hMargin opposing]
  exact WholeQuantileRounding.roundedLaw_security_bound values law _ hOwn hLaw K hK _ hOpposing

end Blotto.WholeQuantileRationalSecurity
