import Blotto.GeneralPaperEqualAddressedClosure

/-! Native measured final reference/control closure. All eleven earlier
component prices and the exact canonical sampler are preserved. Complete
preparation time/space/common-reference joins remain separate obligations. -/
namespace Blotto.GeneralPaperEqualAddressedPreparation
open MeasureTheory
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :=
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
  let routes := GeneralPaperEqualRouteConstruction.prepare packed.1 model A lengths.1 hL
  let full := GeneralPaperEqualNativeSegmentPreparation.prepared r small packed.1 model A
  let cache := GeneralPaperEqualAddressedClosure.run routes.1 full.1 packed.1.groups.data.size packed.1.groups.size model A k budget
  let work : GeneralPaperEqualCompactedPreparation.Work :=
    ⟨raw.2, lengths.2, packed.2, routes.2, full.2, cache.2.1.compaction,
      cache.2.1.integerProduct, cache.2.1.integerCounts, cache.2.1.midpointPower⟩
  (cache.1, ((work, cache.2.1.rejectionWidth, cache.2.1.booleanCache), cache.2.2))

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).1 =
      GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget := by
  unfold run
  dsimp only
  exact GeneralPaperEqualAddressedClosure.data _ _ _ _ model A k budget

theorem previous {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let result := run bits model W A k values v hv small budget
    (result.1, result.2.1) = GeneralPaperEqualClosedPreparation.run bits model W A k values v hv small budget := by
  dsimp only
  apply Prod.ext
  · exact (data bits model W A k values v hv small budget).trans
      (GeneralPaperEqualClosedPreparation.data bits model W A k values v hv small budget).symm
  · rfl

theorem closure_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let result := (run bits model W A k values v hv small budget).2.2
    let b := rationalWordWidth budget
    result.1 + result.2.1 + result.2.2 ≤
      4096 * (b + A + model.rat (8 * (binaryWordWidth n + binaryWordWidth k + binaryWordWidth b + 66)) + 1) := by
  dsimp only
  have hm := GeneralPaperEqualNativeCache.group_count (rounded bits model W k values v hv) small
  have hWord := binaryWordWidth_mono hm
  have h3 : binaryWordWidth 3 = 2 := by decide
  have hArg : GeneralPaperEqualAddressConstruction.operandWidth n
      (terminal (rounded bits model W k values v hv) small).groups.length k (rationalWordWidth budget) ≤
      8 * (binaryWordWidth n + binaryWordWidth k + binaryWordWidth (rationalWordWidth budget) + 66) := by
    unfold GeneralPaperEqualAddressConstruction.operandWidth
    omega
  have hRat := model.monotone hArg
  have h : ∀ (routes : PreparedGroupOutput (terminal (rounded bits model W k values v hv) small).partition)
      (full : PreparedSegmentDescriptor (lottery (rounded bits model W k values v hv) small))
      (size : ℕ) (hSize : size = (terminal (rounded bits model W k values v hv) small).groups.length),
      let result := (GeneralPaperEqualAddressedClosure.run routes full size hSize model A k budget).2
      result.2.1 + result.2.2.1 + result.2.2.2 ≤
        4096 * (rationalWordWidth budget + A + model.rat
          (8 * (binaryWordWidth n + binaryWordWidth k + binaryWordWidth (rationalWordWidth budget) + 66)) + 1) := by
    intro routes full size hSize
    have hw := GeneralPaperEqualAddressedClosure.closure_work routes full size hSize model A k budget
    exact hw.trans (Nat.mul_le_mul_left 4096 (by omega))
  unfold run
  dsimp only
  apply h

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


end Blotto.GeneralPaperEqualAddressedPreparation
