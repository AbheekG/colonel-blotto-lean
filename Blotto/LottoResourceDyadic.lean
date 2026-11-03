import Blotto.LottoResourceSystem
import Blotto.TerminalLottoDyadic
import Blotto.RoundingCDF

/-! The global Lotto resource lottery with finite scalar draws at terminal
states. Its CDF error is uniform in n; all branch probabilities stay exact. -/

namespace Blotto.LottoResourceSystem
open MeasureTheory

noncomputable def dyadicLeafLaw {n : ℕ} (i : LottoResourceSystem n) (K : ℕ) (r : Allocation n) : Mixed n := by
  classical
  exact if hr : i.Valid r then (i.terminal r hr).dyadicLaw K else segmentLaw 0 0

theorem dyadicLeafLaw_CDF_error {n : ℕ} (i : LottoResourceSystem n) (K : ℕ) (r : Allocation n) (hr : i.Valid r) :
    CDFClose (i.dyadicLeafLaw K r) (i.leafLaw r) (3 / (2 * (2 : ℝ) ^ K)) := by
  classical
  rw [dyadicLeafLaw, leafLaw, dite_eq_left hr, dite_eq_left hr]
  exact (i.terminal r hr).dyadicLaw_CDF_error K

theorem dyadicLeafLaw_fullBudget {n : ℕ} (i : LottoResourceSystem n) (K : ℕ) (r : Allocation n) (hr : i.Valid r) :
    ∀ᵐ x ∂(i.dyadicLeafLaw K r : Measure (Allocation n)), FullBudget i.B x := by
  classical
  rw [dyadicLeafLaw, dite_eq_left hr]
  exact (i.terminal r hr).dyadicLaw_fullBudget K

noncomputable def dyadicLaw {n : ℕ} (i : LottoResourceSystem n) (K : ℕ) : Mixed n :=
  i.tree.eval (i.dyadicLeafLaw K)

theorem dyadicLaw_CDF_error {n : ℕ} (i : LottoResourceSystem n) (K : ℕ) :
    CDFClose (i.dyadicLaw K) i.law (3 / (2 * (2 : ℝ) ^ K)) := by
  apply i.tree.eval_CDFClose
  exact i.tree.forLeaves_mono (fun r hr => i.dyadicLeafLaw_CDF_error K r hr) i.tree_valid

theorem dyadicLaw_fullBudget {n : ℕ} (i : LottoResourceSystem n) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation n)), FullBudget i.B x := by
  apply i.tree.eval_fullBudget
  exact i.tree.forLeaves_mono (fun r hr => i.dyadicLeafLaw_fullBudget K r hr) i.tree_valid

theorem dyadicLaw_supported {n : ℕ} (i : LottoResourceSystem n) (K : ℕ) : Supported i.B (i.dyadicLaw K) :=
  (i.dyadicLaw_fullBudget K).mono (fun _ hx => fullBudget_feasible hx)

end Blotto.LottoResourceSystem
