import Blotto.GeneralPaperOriginalExactDrawContract

/-! One actual original-input dispatcher return joins complete preparation
resources with refined direct/circle draw headlines, exact fair-bit counts,
canonical whole laws, every-path hard budgets and whole-player independence.
The direct route consumes no unused shift block. -/
namespace Blotto.GeneralPaperOriginalExactBitHeadlines
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters
set_option autoImplicit false
set_option maxHeartbeats 7500000
set_option maxRecDepth 16384

theorem calibrated_same_return {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧
      GeneralPaperMeasuredJointStorageCalibration.Safe model C d K ∧
      GeneralPaperMeasuredUnequalFullContract.Safe model C d K ∧
      ∃ T t S s D e A a : ℕ, ∀ p : Input, epsilon p < 1 →
        ∃ output : GeneralPaperAllBranchBitDispatch.Prepared p.n,
          (GeneralPaperMeasuredBitDispatch.run model K p).1 = some output ∧
          GeneralPaperAllBranchBitLaw.Guarantee model K p output ∧ GeneralPaperAllBranchBitOutput.Pointwise model K p output ∧
          ((GeneralPaperMeasuredBitDispatch.run model K p).2 : ℚ) ≤
            (T : ℚ) * timeScale p * (logarithm p : ℚ) ^ t ∧
          GeneralPaperOriginalStorageContract.Contract model K S s D e p output ∧
          GeneralPaperOriginalSamplingContract.Contract model C d K p output ∧
          GeneralPaperOriginalExactDrawContract.Contract model C d K A a p output := by
  obtain ⟨K, hK, cal, hWord, hSafe, hNativeSafe, T, t, S, s, D, e, hAll⟩ :=
    GeneralPaperOriginalSamplingContract.calibrated_same_return hg
  obtain ⟨A, a, hDraw⟩ := GeneralPaperOriginalExactDrawContract.uniform hg K
  refine ⟨K, hK, cal, hWord, hSafe, hNativeSafe, T, t, S, s, D, e, A, a, fun p hOne => ?_⟩
  obtain ⟨output, hReturn, hGame, hPointwise, hTime, hStorage, hSampling⟩ := hAll p hOne
  exact ⟨output, hReturn, hGame, hPointwise, hTime, hStorage, hSampling, hDraw p output hOne hReturn hSampling⟩

end Blotto.GeneralPaperOriginalExactBitHeadlines
