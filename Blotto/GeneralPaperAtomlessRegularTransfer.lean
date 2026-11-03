import Blotto.RichSmoothingApproximation

/-! The manuscript's regularity condition asks only for atomless marginals.
The previously constructed positive, full-budget smooth laws satisfy this
condition and already approximate every continuous security response. -/
namespace Blotto.GeneralPaperAtomlessRegularTransfer
open MeasureTheory RichSmoothingLaw RichSmoothingApproximation
set_option autoImplicit false

def AtomlessMarginals {n : ℕ} (law : Mixed n) : Prop :=
  ∀ j z, (marginal law j : Measure ℝ) {z} = 0

theorem rich_regular_atomless {n : ℕ} {budget : ℝ} {law : Mixed n}
    (h : Regular budget law) : AtomlessMarginals law := h.2

theorem exists_atomless_near_security {n : ℕ} (values : Values n) {A B : ℝ}
    (hA : 0 < A) (hn : 2 ≤ n) (hBudgets : B < A)
    (opponent : Mixed n) (hOpponent : Supported B opponent) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ law : Mixed n, Supported A law ∧ AtomlessMarginals law ∧
      security values A opponent - epsilon < expected values law opponent := by
  obtain ⟨law,hRegular,hPayoff⟩ :=
    exists_regular_near_security values hA hn hBudgets opponent hOpponent epsilon he
  exact ⟨law,regular_supported hRegular,rich_regular_atomless hRegular,hPayoff⟩

theorem exists_atomless_continuous_response {n : ℕ} (values : Values n) {A B : ℝ}
    (hA : 0 < A) (hn : 2 ≤ n) (hBudgets : B < A)
    (opponent : Mixed n) (hOpponent : Supported B opponent) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ law : Mixed n, Supported A law ∧ AtomlessMarginals law ∧
      Continuous (fun response : Mixed n => expected values law response) ∧
      security values A opponent - epsilon < expected values law opponent := by
  obtain ⟨law,hRegular,hPayoff⟩ :=
    exists_regular_near_security values hA hn hBudgets opponent hOpponent epsilon he
  exact ⟨law,regular_supported hRegular,rich_regular_atomless hRegular,
    regular_rich_expected_continuous values law hRegular,hPayoff⟩

end Blotto.GeneralPaperAtomlessRegularTransfer
