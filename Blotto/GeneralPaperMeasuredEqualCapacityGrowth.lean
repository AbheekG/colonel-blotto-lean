import Blotto.GeneralPaperMeasuredEqualDispatchStorage

/-! Uniform capacity growth for the complete equal dispatcher envelope,
including its actual smaller-charge initializer and resident RAM. -/
namespace Blotto.GeneralPaperMeasuredEqualCapacityGrowth
open GeneralPaperEqualInputDomain
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

theorem uniform_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ D : ℕ, ∀ (p : Input model) (W K : ℕ),
      binaryWordWidth (GeneralPaperMeasuredEqualDispatchStorage.envelope model W K p) ≤
        D * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨A, hE⟩ := GeneralPaperStoredPreparationUniformCapacity.envelope_small model hFast
  obtain ⟨B, hI⟩ := GeneralPaperMixedInitializerCalibration.uniform_word_growth model hFast
  obtain ⟨F, hF⟩ := GeneralPaperMeasuredEqualDispatchFrame.branch_small model hFast
  refine ⟨A + B + F + 32, fun p W K => ?_⟩
  have he := hE ⟨p, W, K⟩
  change binaryWordWidth (GeneralPaperStoredPreparationUniformCapacity.envelope model K p) ≤
    A * (logarithm p + binaryWordWidth W + binaryWordWidth K) at he
  have hi := hI p W K
  have hf := hF p
  have h0 := GeneralPaperReferenceScaling.word_add (GeneralPaperStoredPreparationUniformCapacity.envelope model K p)
    (GeneralPaperMixedInitializerPhases.profile model W K p)
  have h1 := GeneralPaperReferenceScaling.word_add
    (GeneralPaperStoredPreparationUniformCapacity.envelope model K p + GeneralPaperMixedInitializerPhases.profile model W K p) W
  have h2 := GeneralPaperReferenceScaling.word_add
    (GeneralPaperStoredPreparationUniformCapacity.envelope model K p + GeneralPaperMixedInitializerPhases.profile model W K p + W)
    (GeneralPaperMeasuredEqualDispatchFrame.branchPrice model p)
  have h3 := GeneralPaperReferenceScaling.word_add
    (GeneralPaperStoredPreparationUniformCapacity.envelope model K p + GeneralPaperMixedInitializerPhases.profile model W K p + W +
      GeneralPaperMeasuredEqualDispatchFrame.branchPrice model p) 1
  have h4 := binaryWordWidth_mul 32768
    (GeneralPaperStoredPreparationUniformCapacity.envelope model K p + GeneralPaperMixedInitializerPhases.profile model W K p + W +
      GeneralPaperMeasuredEqualDispatchFrame.branchPrice model p + 1)
  rw [show binaryWordWidth 1 = 1 by decide] at h3
  rw [show binaryWordWidth 32768 = 16 by decide] at h4
  have hL := logarithm_positive p
  change binaryWordWidth (32768 * _) ≤ _
  nlinarith only [he, hi, hf, h0, h1, h2, h3, h4, hL,
    Nat.zero_le (binaryWordWidth W), Nat.zero_le (binaryWordWidth K)]

end Blotto.GeneralPaperMeasuredEqualCapacityGrowth
