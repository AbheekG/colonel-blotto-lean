import Blotto.NestedResourceSystem
import Blotto.TerminalResourcesDyadic
import Blotto.RoundingCDF

/-! The at-most-two-update resource lottery uses finite terminal nested
laws, retaining their common CDF error, budget, and coordinate-box support. -/

namespace Blotto.NestedResourceSystem
open MeasureTheory

noncomputable def dyadicLeafLaw (i : NestedResourceSystem) (K : ℕ) (r : Allocation 3) : Mixed 3 := by
  classical
  exact if hr : i.Valid r then (i.terminal r hr).dyadicLaw K else segmentLaw 0 0

theorem dyadicLeafLaw_CDF_error (i : NestedResourceSystem) (K : ℕ) (r : Allocation 3) (hr : i.Valid r) :
    CDFClose (i.dyadicLeafLaw K r) (i.leafLaw r) (3 / (2 * (2 : ℝ) ^ K)) := by
  classical
  rw [dyadicLeafLaw, leafLaw, dite_eq_left hr, dite_eq_left hr]
  exact (i.terminal r hr).dyadicLaw_CDF_error K

theorem dyadicLeafLaw_fullBudget (i : NestedResourceSystem) (K : ℕ) (r : Allocation 3) (hr : i.Valid r) :
    ∀ᵐ x ∂(i.dyadicLeafLaw K r : Measure (Allocation 3)), FullBudget i.M x := by
  classical
  rw [dyadicLeafLaw, dite_eq_left hr]
  exact (i.terminal r hr).dyadicLaw_fullBudget K

theorem dyadicLeafLaw_inBox (i : NestedResourceSystem) (K : ℕ) (r : Allocation 3) (hr : i.Valid r) :
    ∀ᵐ x ∂(i.dyadicLeafLaw K r : Measure (Allocation 3)), InBox i.long x := by
  classical
  rw [dyadicLeafLaw, dite_eq_left hr]
  exact (i.terminal r hr).dyadicLaw_inBox K

noncomputable def dyadicLaw (i : NestedResourceSystem) (K : ℕ) : Mixed 3 := i.tree.eval (i.dyadicLeafLaw K)

theorem dyadicLaw_CDF_error (i : NestedResourceSystem) (K : ℕ) :
    CDFClose (i.dyadicLaw K) i.law (3 / (2 * (2 : ℝ) ^ K)) := by
  apply i.tree.eval_CDFClose
  exact i.tree.forLeaves_mono (fun r hr => i.dyadicLeafLaw_CDF_error K r hr) i.tree_valid

theorem dyadicLaw_fullBudget (i : NestedResourceSystem) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation 3)), FullBudget i.M x := by
  apply i.tree.eval_fullBudget
  exact i.tree.forLeaves_mono (fun r hr => i.dyadicLeafLaw_fullBudget K r hr) i.tree_valid

theorem dyadicLaw_inBox (i : NestedResourceSystem) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation 3)), InBox i.long x := by
  apply i.tree.eval_inBox
  exact i.tree.forLeaves_mono (fun r hr => i.dyadicLeafLaw_inBox K r hr) i.tree_valid

end Blotto.NestedResourceSystem
