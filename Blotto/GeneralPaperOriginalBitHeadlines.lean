import Blotto.GeneralPaperOriginalDrawContract

/-! Uniform preparation resources and final original-input draw rates on
one actual returned description. The real entry retains its separately
proved numeric-input contract. Direct-route unused-shift elimination is a
separate refinement of the retained sampler, preserving all these results. -/
namespace Blotto.GeneralPaperOriginalBitHeadlines
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
          GeneralPaperOriginalDrawContract.Contract model K A a p output := by
  obtain ⟨K, hK, cal, hWord, hSafe, hNativeSafe, T, t, S, s, D, e, hAll⟩ :=
    GeneralPaperOriginalSamplingContract.calibrated_same_return hg
  obtain ⟨A, a, hDraw⟩ := GeneralPaperOriginalDrawContract.uniform hg K
  refine ⟨K, hK, cal, hWord, hSafe, hNativeSafe, T, t, S, s, D, e, A, a, fun p hOne => ?_⟩
  obtain ⟨output, hReturn, hGame, hPointwise, hTime, hStorage, hSampling⟩ := hAll p hOne
  exact ⟨output, hReturn, hGame, hPointwise, hTime, hStorage, hSampling, hDraw p output hSampling⟩

end Blotto.GeneralPaperOriginalBitHeadlines
