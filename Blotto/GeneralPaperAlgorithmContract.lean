import Blotto.GeneralPaperAllBranchExactRealSampling

/-! One entry theorem joins the paper's numeric-real and encoded-rational
bit computational models, preserving the actual original-input producers
and refined direct/circle sampler. Proof/English correspondence is audited
separately; this is not a claim that every paper statement is covered. -/
namespace Blotto.GeneralPaperAlgorithmContract
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem real_and_bit {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧
      GeneralPaperMeasuredJointStorageCalibration.Safe model C d K ∧
      GeneralPaperMeasuredUnequalFullContract.Safe model C d K ∧
      ∃ T t S s D e A a R r : ℕ,
      (∀ p : Input, epsilon p < 1 →
        ∃ output : GeneralPaperAllBranchBitDispatch.Prepared p.n,
          (GeneralPaperMeasuredBitDispatch.run model K p).1 = some output ∧
          GeneralPaperAllBranchBitLaw.Guarantee model K p output ∧ GeneralPaperAllBranchBitOutput.Pointwise model K p output ∧
          ((GeneralPaperMeasuredBitDispatch.run model K p).2 : ℚ) ≤
            (T : ℚ) * timeScale p * (logarithm p : ℚ) ^ t ∧
          GeneralPaperOriginalStorageContract.Contract model K S s D e p output ∧
          GeneralPaperOriginalSamplingContract.Contract model C d K p output ∧
          GeneralPaperOriginalExactDrawContract.Contract model C d K A a p output) ∧
      ∀ p : GeneralPaperOriginalRealInput.Input,
        ((GeneralPaperAllBranchRealDispatch.run model p).2 : ℚ) ≤
          (R : ℚ) * GeneralPaperRealHeadlineParameters.timeScale p.n p.epsilon *
            (GeneralPaperRealHeadlineParameters.logarithm p.n p.epsilon : ℚ) ^ r ∧
        GeneralPaperAllBranchExactRealLaw.Guarantee model p (GeneralPaperAllBranchRealDispatch.run model p).1 ∧
        GeneralPaperAllBranchExactRealLaw.Pointwise model p (GeneralPaperAllBranchRealDispatch.run model p).1 ∧
        GeneralPaperAllBranchExactRealSampling.Contract model p (GeneralPaperAllBranchRealDispatch.run model p).1 := by
  obtain ⟨K, hK, cal, hWord, hSafe, hNativeSafe, T, t, S, s, D, e, A, a, hBit⟩ :=
    GeneralPaperOriginalExactBitHeadlines.calibrated_same_return hg
  obtain ⟨R, r, hReal⟩ := GeneralPaperAllBranchExactRealSampling.time_game_and_sampling model
  exact ⟨K, hK, cal, hWord, hSafe, hNativeSafe, T, t, S, s, D, e, A, a, R, r, hBit, hReal⟩

end Blotto.GeneralPaperAlgorithmContract
