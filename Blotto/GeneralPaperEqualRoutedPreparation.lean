import Blotto.GeneralPaperEqualRoutedCache

/-! The actual native preparation now consumes measured cached routes once.
All three previous price fields are preserved exactly, with one additional
route field. Remaining cache/closure prices and complete lifetime are open. -/
namespace Blotto.GeneralPaperEqualRoutedPreparation
open MeasureTheory
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    GeneralPaperEqualStoredBitSampler.Sampler (terminal (rounded bits model W k values v hv) small).partition
      (lottery (rounded bits model W k values v hv) small) × (ℕ × ℕ × ℕ × ℕ) :=
  let raw := GeneralPaperValueRoundingPaperContract.run bits model W 128 k values
  let hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 128 k (by decide) values v hv
  let r := GeneralPaperNativeRationalValues.selector raw.1.2 hp.1 raw.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 128 k values)
  let i := terminal r small
  let lengths := GeneralPaperEqualLengthArray.run model A raw.1.1 raw.1.2
  let hL : ∀ j, lengths.1.read j = i.length j := by
    intro j
    rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]
    rfl
  let packed := GeneralPaperEqualMaterializedPacking.run i model A lengths.1 hL (List.finRange n)
    (GeneralPaperEqualPreparationPrefix.uniform_items r small).symm
  let hPacked := GeneralPaperEqualMaterializedPacking.data i model A lengths.1 hL (List.finRange n)
    (GeneralPaperEqualPreparationPrefix.uniform_items r small).symm
  let routes := GeneralPaperEqualRouteConstruction.prepare packed.1 model A lengths.1 hL
  let hRoutes := GeneralPaperEqualRouteConstruction.prepare_data packed.1 model A lengths.1 hL
  let sampler := GeneralPaperEqualRoutedCache.close r small packed.1 hPacked routes.1 hRoutes k budget
  (sampler, (raw.2, lengths.2, packed.2, routes.2))

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).1 =
      GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget := by
  unfold run
  dsimp only
  exact (GeneralPaperEqualRoutedCache.close_eq _ _ _ _ _ _ k budget).trans
    (GeneralPaperEqualPackedCache.close_eq _ _ _ _ k budget)

theorem previous {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let result := run bits model W A k values v hv small budget
    (result.1, (result.2.1, result.2.2.1, result.2.2.2.1)) =
      GeneralPaperEqualPreparationPrefix.run bits model W A k values v hv small budget := by
  dsimp only
  apply Prod.ext
  · exact (data bits model W A k values v hv small budget).trans
      (GeneralPaperEqualPreparationPrefix.data bits model W A k values v hv small budget).symm
  · rfl

theorem route_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).2.2.2.2 ≤
      64 * (n + 1) * model.rat (4 * (binaryWordWidth n + k + 9) + 3) +
        4096 * (n + 1) * (A + binaryWordWidth (n + 1) + 1) := by
  unfold run
  dsimp only
  apply GeneralPaperEqualNativeRouteCost.native_work bits model W A k values v hv small

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

end Blotto.GeneralPaperEqualRoutedPreparation
