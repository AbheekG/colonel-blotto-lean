import Blotto.GeneralPaperOriginalHeadlineTransfers

/-! The one-field branch returns the exact pure equilibrium before any
accuracy/source preparation. Its actual bit work is input-linear. -/
namespace Blotto.GeneralPaperOneFieldOriginalResources
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters
open GeneralPaperAllBranchBitDispatch (one)
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

theorem work (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) :
    (GeneralPaperMeasuredBitDispatch.run model K p).2 ≤ 2048 * inputSize p := by
  have h := GeneralPaperMeasuredDispatchResources.one_work model K p hN
  have hWidth : binaryWordWidth p.n = 1 := by rw [hN]; decide
  rw [hWidth] at h
  have hi : rationalWordWidth p.budget + 1 ≤ inputSize p := by unfold inputSize; omega
  omega

theorem time (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) :
    ((GeneralPaperMeasuredBitDispatch.run model K p).2 : ℚ) ≤
      2048 * timeScale p * (logarithm p : ℚ) ^ 0 := by
  have h : ((GeneralPaperMeasuredBitDispatch.run model K p).2 : ℚ) ≤ 2048 * (inputSize p : ℚ) := by
    exact_mod_cast work model K p hN
  have hm := mul_le_mul_of_nonneg_left (time_ge_input p) (by norm_num : (0 : ℚ) ≤ 2048)
  simpa only [pow_zero, mul_one] using h.trans hm

theorem exact_regrets (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) :
    regret p.selector.values 1 (GeneralPaperAllBranchBitLaw.law model K p (one p hN).1 false)
      (GeneralPaperAllBranchBitLaw.law model K p (one p hN).1 true) = 0 ∧
    regret p.selector.values (p.budget : ℝ) (GeneralPaperAllBranchBitLaw.law model K p (one p hN).1 true)
      (GeneralPaperAllBranchBitLaw.law model K p (one p hN).1 false) = 0 := by
  rcases p with ⟨n, values, selector, correct, words, b, hBudget⟩
  change n = 1 at hN
  subst n
  have h := GeneralPaperOneFieldRealPreparation.equilibrium selector.values 1 b (by norm_num) hBudget.1.le
  dsimp only at h
  simp only [Rat.cast_one] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

theorem actual_return (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) :
    (GeneralPaperMeasuredBitDispatch.run model K p).1 = some (one p hN).1 ∧
    GeneralPaperAllBranchBitOutput.Pointwise model K p (one p hN).1 ∧
    regret p.selector.values 1 (GeneralPaperAllBranchBitLaw.law model K p (one p hN).1 false)
      (GeneralPaperAllBranchBitLaw.law model K p (one p hN).1 true) = 0 ∧
    regret p.selector.values (p.budget : ℝ) (GeneralPaperAllBranchBitLaw.law model K p (one p hN).1 true)
      (GeneralPaperAllBranchBitLaw.law model K p (one p hN).1 false) = 0 ∧
    (GeneralPaperMeasuredBitDispatch.run model K p).2 ≤ 2048 * inputSize p := by
  exact ⟨by rw [GeneralPaperMeasuredBitDispatch.on_one model K p hN],
    GeneralPaperAllBranchBitOutput.one_outputs model K p hN,
    (exact_regrets model K p hN).1, (exact_regrets model K p hN).2, work model K p hN⟩

end Blotto.GeneralPaperOneFieldOriginalResources
