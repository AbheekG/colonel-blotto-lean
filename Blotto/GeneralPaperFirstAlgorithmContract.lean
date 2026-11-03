import Blotto.GeneralPaperFirstUniformListReturns

/-! The paper entry theorem with the revised uniform-list sampling
statement joined to the same actual real and bit returns. The list view is
erased; all execution and sharp resource contracts remain the checked ones. -/
namespace Blotto.GeneralPaperFirstAlgorithmContract
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem actual_contract {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧
      GeneralPaperFirstSharedResourceCalibration.EqualSafe model K ∧
      GeneralPaperMeasuredJointStorageCalibration.Safe model C d K ∧
      GeneralPaperMeasuredUnequalFullContract.Safe model C d K ∧
      ∃ T t S s D e A a R r : ℕ,
      (∀ p : Input, epsilon p < 1 →
        ∃ output : GeneralPaperAllBranchBitDispatch.Prepared p.n,
          (GeneralPaperFirstAllBitDispatch.run model K p).1 = some output ∧
          GeneralPaperFirstAllBitLaw.Guarantee model K p output ∧ GeneralPaperFirstAllBitLaw.Pointwise model K p output ∧
          ((GeneralPaperFirstAllBitDispatch.run model K p).2 : ℚ) ≤
            (T : ℚ) * timeScale p * (logarithm p : ℚ) ^ t ∧
          GeneralPaperFirstOriginalStorageContract.Contract model K S s D e p output ∧
          GeneralPaperFirstOriginalSamplingContract.Contract model C d K p output ∧
          GeneralPaperFirstOriginalExactDrawContract.Contract model C d K A a p output ∧
          GeneralPaperUniformListReturns.Bit p output) ∧
      ∀ p : GeneralPaperOriginalRealInput.Input,
        ((GeneralPaperFirstAllRealDispatch.run model p).2 : ℚ) ≤
          (R : ℚ) * GeneralPaperRealHeadlineParameters.timeScale p.n p.epsilon *
            (GeneralPaperRealHeadlineParameters.logarithm p.n p.epsilon : ℚ) ^ r ∧
        GeneralPaperFirstAllExactRealLaw.Guarantee model p (GeneralPaperFirstAllRealDispatch.run model p).1 ∧
        GeneralPaperFirstAllExactRealLaw.Pointwise model p (GeneralPaperFirstAllRealDispatch.run model p).1 ∧
        GeneralPaperFirstAllExactRealSampling.Contract model p (GeneralPaperFirstAllRealDispatch.run model p).1 ∧
        GeneralPaperFirstRealAlgorithmContract.UniformList model p (GeneralPaperFirstAllRealDispatch.run model p).1 := by
  obtain ⟨K, hK, cal, hWord, hEqualSafe, hSafe, hNativeSafe, T, t, S, s, D, e, A, a, hBit⟩ :=
    GeneralPaperFirstOriginalExactBitHeadlines.calibrated_same_return hg
  obtain ⟨R, r, hReal⟩ := GeneralPaperFirstAllExactRealSampling.time_game_and_sampling model
  refine ⟨K, hK, cal, hWord, hEqualSafe, hSafe, hNativeSafe, T, t, S, s, D, e, A, a, R, r, ?_, ?_⟩
  · intro p hOne
    obtain ⟨output, hReturn, hGame, hPointwise, hTime, hStorage, hSampling, hExact⟩ := hBit p hOne
    exact ⟨output, hReturn, hGame, hPointwise, hTime, hStorage, hSampling, hExact,
      GeneralPaperFirstUniformListReturns.bit_of_sampling p hOne output hReturn hSampling⟩
  · intro p
    have h := hReal p
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, GeneralPaperFirstRealAlgorithmContract.uniform_list model p⟩

end Blotto.GeneralPaperFirstAlgorithmContract
