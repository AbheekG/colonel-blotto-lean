import Blotto.GeneralPaperOriginalReferenceComparison

/-! One fixed program coefficient simultaneously covers the complete equal
preparation envelope and any prescribed linear original-input word floor.
The envelope is erased; execution measures lengths and multiplies by K. -/
namespace Blotto.GeneralPaperAllBranchReferenceCalibration
open GeneralPaperOriginalGameInput
open GeneralPaperOriginalReferenceComparison (logarithm)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem uniform_above (model : RationalCostModel)
    (hFast : GeneralPaperFastRationalModel.IsFast model) (lower : ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : Input,
      GeneralPaperStoredPreparationUniformCapacity.envelope model K (equalInput model p) <
        2 ^ (K * logarithm model p) ∧ lower * logarithm model p < K * logarithm model p := by
  obtain ⟨C, hC⟩ := GeneralPaperStoredPreparationUniformCapacity.envelope_small model hFast
  let P := fun (_W K : ℕ) (p : Input) =>
    GeneralPaperStoredPreparationUniformCapacity.envelope model K (equalInput model p) +
      2 ^ (lower * logarithm model p)
  have hGrowth : ∃ D : ℕ, ∀ (p : Input) (W K : ℕ),
      binaryWordWidth (P W K p) ≤ D *
        (logarithm model p + binaryWordWidth W + binaryWordWidth K) := by
    refine ⟨C + (lower + 1), fun p W K => ?_⟩
    have hEnvelope := hC ⟨equalInput model p, W, K⟩
    change binaryWordWidth (GeneralPaperStoredPreparationUniformCapacity.envelope model K
      (equalInput model p)) ≤ C * (logarithm model p + binaryWordWidth W + binaryWordWidth K) at hEnvelope
    have hL := GeneralPaperEqualInputDomain.logarithm_positive (equalInput model p)
    change 1 ≤ logarithm model p at hL
    have hTail : binaryWordWidth (2 ^ (lower * logarithm model p)) ≤
        (lower + 1) * (logarithm model p + binaryWordWidth W + binaryWordWidth K) := by
      simp only [binaryWordWidth, Nat.log2_two_pow]
      nlinarith only [hL, Nat.zero_le (binaryWordWidth W), Nat.zero_le (binaryWordWidth K)]
    exact (GeneralPaperReferenceScaling.word_add _ _).trans
      ((Nat.add_le_add hEnvelope hTail).trans_eq (by ring))
  obtain ⟨K, hK, hSafe⟩ := GeneralPaperSelfReferenceCapacity.uniform_capacity P (logarithm model)
    (fun p => GeneralPaperEqualInputDomain.logarithm_positive (equalInput model p)) hGrowth
  refine ⟨K, hK, fun p => ?_⟩
  have hs := hSafe p
  dsimp only [P] at hs
  have hPositive : 0 < (2 : ℕ) ^ (lower * logarithm model p) := by positivity
  refine ⟨by omega, ?_⟩
  by_contra hn
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_of_not_gt hn)
  omega

theorem uniform_calibration {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : Input,
      GeneralPaperStoredPreparationUniformCapacity.envelope model K (equalInput model p) <
        2 ^ (K * logarithm model p) ∧ ∀ h : p.budget < 1,
      GeneralPaperNativeResourceReferenceGrowth.word model C d (unequalInput p h) ≤ K * logarithm model p := by
  obtain ⟨J, hJ⟩ := GeneralPaperNativeResourceReferenceGrowth.word_tight hg
  obtain ⟨K, hK, hSafe⟩ := uniform_above model ⟨C, d, hg⟩ (8 * J)
  refine ⟨K, hK, fun p => ⟨(hSafe p).1, fun h => ?_⟩⟩
  calc
    _ ≤ J * GeneralPaperNativeResourceDomain.logarithm model (unequalInput p h) := hJ _
    _ ≤ J * (8 * logarithm model p) :=
      Nat.mul_le_mul_left J (GeneralPaperOriginalReferenceComparison.native_log_le model p h)
    _ = (8 * J) * logarithm model p := by ring
    _ ≤ K * logarithm model p := (hSafe p).2.le

end Blotto.GeneralPaperAllBranchReferenceCalibration
