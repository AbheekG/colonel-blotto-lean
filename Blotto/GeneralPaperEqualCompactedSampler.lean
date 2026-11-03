import Blotto.GeneralPaperEqualCompactedPreparation

/-! The measured preparation returns the established sampler and its exact
canonical law/description. The nine retained component prices exclude the
existing Boolean/width/address closure; no full preparation claim is made. -/
namespace Blotto.GeneralPaperEqualCompactedSampler
open MeasureTheory
open GeneralPaperEqualNativeSampler (rounded)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :=
  let prepared := GeneralPaperEqualCompactedPreparation.run bits model W A k values v hv small budget
  let h : prepared.1.midpointBits = k + 5 := by
    rw [GeneralPaperEqualCompactedPreparation.data]
    rfl
  (GeneralPaperEqualStoredBitSampler.prepare prepared.1 k h, prepared.2)

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).1 =
      GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget := by
  unfold run
  dsimp only
  exact GeneralPaperEqualCachedPreparation.sampler_eq _ _ k _ rfl
    (GeneralPaperEqualCompactedPreparation.data bits model W A k values v hv small budget)

theorem previous {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let result := run bits model W A k values v hv small budget
    (result.1, (result.2.rounding, result.2.lengths, result.2.packing, result.2.routes)) =
      GeneralPaperEqualRoutedPreparation.run bits model W A k values v hv small budget := by
  dsimp only
  apply Prod.ext
  · exact (data bits model W A k values v hv small budget).trans
      (GeneralPaperEqualRoutedPreparation.data bits model W A k values v hv small budget).symm
  · rfl

theorem epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (small : ∀ j, 2 * (rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 < budget) :
    let sampler := (run bits model W A (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget).1
    Supported (budget : ℝ) (GeneralPaperEqualStoredBitSampler.outputLaw sampler model) ∧
      regret v.values (budget : ℝ) (GeneralPaperEqualStoredBitSampler.outputLaw sampler model)
        (GeneralPaperEqualStoredBitSampler.outputLaw sampler model) ≤ (eps : ℝ) := by
  dsimp only
  rw [data]
  exact GeneralPaperEqualStoredBitSampler.native_epsilon bits model W values v hv eps hp hOne small budget hB

theorem description {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let b := rationalWordWidth budget
    let R := GeneralPaperEqualDescriptionRates.reference n k b
    GeneralPaperEqualRetainedStorage.footprint R (run bits model W A k values v hv small budget).1 ≤
      GeneralPaperEqualDescriptionRates.paperBound n k b ∧
      GeneralPaperEqualRetainedStorage.footprint R (run bits model W A k values v hv small budget).1 < 2 ^ R := by
  dsimp only
  rw [data]
  exact GeneralPaperEqualDescriptionRates.native_paper_description bits model W k values v hv small budget

end Blotto.GeneralPaperEqualCompactedSampler
