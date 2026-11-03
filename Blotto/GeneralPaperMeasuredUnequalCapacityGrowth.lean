import Blotto.GeneralPaperMeasuredUnequalCapacityEnvelope

/-! Uniform logarithmic growth of the complete unequal capacity envelope,
simultaneously in the physical reference and the fixed program coefficient. -/
namespace Blotto.GeneralPaperMeasuredUnequalCapacityGrowth
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperUniformResourceGrowth
open GeneralPaperMeasuredUnequalCapacityEnvelope (branch envelope)
open GeneralPaperMeasuredUnequalCounterCapacity (initProfile)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

theorem branch_small {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) : Small (branch model) (logarithm model) := by
  have hL := logarithm_positive model
  have hn := count_small model
  have hb : Small (fun p : Problem => rationalWordWidth p.budget) (logarithm model) :=
    small_below_ledger model _ (fun p => by unfold ledger originalInputSize; omega)
  have hp := primitive_small hg (fun p : Problem => rationalWordWidth p.budget + 3) (logarithm model) hL (by fun_prop)
  change Small (fun p : Problem => model.rat (rationalWordWidth p.budget + 3) +
    64 * (binaryWordWidth p.n + 1)) (logarithm model)
  fun_prop

theorem reserve_word_growth {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ D : ℕ, ∀ (p : Problem) (W : ℕ),
      binaryWordWidth (reserve model C d W p) ≤ D * (logarithm model p + binaryWordWidth W) := by
  obtain ⟨A, hA⟩ := reserve_at_one_small hg
  refine ⟨A + 2, fun p W => ?_⟩
  have hs := GeneralPaperFullPreparationReference.scaling model C d (accuracySize p) (exponent p) (originalSize p)
    (prepared model p).Qv (ledger p) (height model p) (reduced model p) (source model p)
  change GeneralPaperReferenceScaling.Scale (fun S => reserve model C d S p) at hs
  have hm : reserve model C d W p ≤ (W + 1) * reserve model C d 1 p :=
    (hs.1 (Nat.le_succ W)).trans (by simpa only [Nat.mul_one] using hs.2 (W + 1) 1 (by omega))
  have hb := (binaryWordWidth_mono hm).trans (binaryWordWidth_mul (W + 1) (reserve model C d 1 p))
  have hw := GeneralPaperReferenceScaling.word_add W 1
  rw [show binaryWordWidth 1 = 1 by decide] at hw
  have hBase := hA p
  have hL := logarithm_positive model p
  nlinarith only [hb, hw, hBase, hL, Nat.zero_le (binaryWordWidth W)]

theorem uniform_word_growth {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ D : ℕ, ∀ (p : Problem) (W K : ℕ), binaryWordWidth (envelope model C d W K p) ≤
      D * (logarithm model p + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨A, hI⟩ := GeneralPaperMixedInitializerCalibration.uniform_word_growth model ⟨C, d, hg⟩
  obtain ⟨B, hR⟩ := reserve_word_growth hg
  obtain ⟨F, hF⟩ := small_bits (branch model) (logarithm model) (logarithm_positive model) (branch_small hg)
  refine ⟨2 * A + B + F + 32, fun p W K => ?_⟩
  let ep := GeneralPaperOriginalGameInput.equalInput model (GeneralPaperMeasuredReferenceGrowth.original p)
  have hi := hI ep W K
  have hl : GeneralPaperEqualInputDomain.logarithm ep ≤ 2 * logarithm model p :=
    GeneralPaperOriginalReferenceComparison.measured_log_le model (GeneralPaperMeasuredReferenceGrowth.original p) p.budget_valid.2
  have hi' : binaryWordWidth (initProfile model W K p) ≤
      A * (2 * logarithm model p + binaryWordWidth W + binaryWordWidth K) :=
    hi.trans (Nat.mul_le_mul_left A (by omega))
  have hr := hR p W
  have hf := hF p
  have h0 := GeneralPaperReferenceScaling.word_add (initProfile model W K p) (reserve model C d W p)
  have h1 := GeneralPaperReferenceScaling.word_add (initProfile model W K p + reserve model C d W p) W
  have h2 := GeneralPaperReferenceScaling.word_add (initProfile model W K p + reserve model C d W p + W)
    (GeneralPaperEncodedScalarStorage.natBits (branch model p))
  have h3 := GeneralPaperReferenceScaling.word_add
    (initProfile model W K p + reserve model C d W p + W + GeneralPaperEncodedScalarStorage.natBits (branch model p)) 1
  have h4 := binaryWordWidth_mul 16384
    (initProfile model W K p + reserve model C d W p + W + GeneralPaperEncodedScalarStorage.natBits (branch model p) + 1)
  rw [show binaryWordWidth 1 = 1 by decide] at h3
  rw [show binaryWordWidth 16384 = 15 by decide] at h4
  have hL := logarithm_positive model p
  change binaryWordWidth (16384 * _) ≤ _
  nlinarith only [hi', hr, hf, h0, h1, h2, h3, h4, hL,
    Nat.zero_le (binaryWordWidth W), Nat.zero_le (binaryWordWidth K)]

end Blotto.GeneralPaperMeasuredUnequalCapacityGrowth
