import Blotto.GeneralPaperEqualBitVertex

/-! Resume grouped bit preparation from the actual retained length array.
Packing, routes, segments and full measured closure execute once. The first
two source stages are not repeated or hidden inside this continuation. -/
namespace Blotto.GeneralPaperEqualBitContinuation
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperEqualNativeSampler (rounded)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def run {n : ℕ} (model : RationalCostModel) (A k : ℕ) (v : RationalFieldSelector n)
    (small : ∀ j, 2 * v.weight j ≤ 1) (lengths : FixedArrayTable n ℚ)
    (hL : ∀ j, lengths.read j = (terminal v small).length j) (budget : ℚ) :=
  let packed := GeneralPaperEqualMaterializedPacking.run (terminal v small) model A lengths hL (List.finRange n)
    (GeneralPaperEqualPreparationPrefix.uniform_items v small).symm
  let routes := GeneralPaperEqualRouteConstruction.prepare packed.1 model A lengths hL
  let full := GeneralPaperEqualNativeSegmentPreparation.prepared v small packed.1 model A
  let cache := GeneralPaperEqualAddressedClosure.run routes.1 full.1 packed.1.groups.data.size packed.1.groups.size model A k budget
  let w := cache.2.1
  (cache.1, packed.2 + routes.2 + full.2 + w.compaction + (w.integerProduct + w.integerCounts) +
    w.midpointPower + w.rejectionWidth + w.booleanCache + (cache.2.2.1 + cache.2.2.2.1 + cache.2.2.2.2))

theorem data {n : ℕ} (model : RationalCostModel) (A k : ℕ) (v : RationalFieldSelector n)
    (small : ∀ j, 2 * v.weight j ≤ 1) (lengths : FixedArrayTable n ℚ)
    (hL : ∀ j, lengths.read j = (terminal v small).length j) (budget : ℚ) :
    (run model A k v small lengths hL budget).1 = GeneralPaperEqualStoredBitSampler.prepare
      (GeneralPaperEqualPreparedCache.prepare (terminal v small).partition (lottery v small) (k + 5) budget) k rfl := by
  unfold run
  dsimp only
  exact GeneralPaperEqualAddressedClosure.data _ _ _ _ model A k budget

def native {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :=
  let raw := (GeneralPaperValueRoundingPaperContract.run true model W 128 k values).1
  let lengths := GeneralPaperEqualLengthArray.run model A raw.1 raw.2
  let hL : ∀ j, lengths.1.read j = (terminal (rounded true model W k values v hv) small).length j := by
    intro j; rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]; rfl
  run model A k (rounded true model W k values v hv) small lengths.1 hL budget

theorem native_data {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (native model W A k values v hv small budget).1 =
      GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget := by
  unfold native
  dsimp only
  exact data model A k _ small _ _ budget

theorem price_join {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let raw := GeneralPaperValueRoundingPaperContract.run true model W 128 k values
    let lengths := GeneralPaperEqualLengthArray.run model A raw.1.1 raw.1.2
    let work := (GeneralPaperEqualAddressedPreparation.run true model W A k values v hv small budget).2
    GeneralPaperEqualBitPreparationLedger.total work.1.1 work.1.2.1 work.1.2.2 work.2.1 work.2.2.1 work.2.2.2 =
      raw.2 + lengths.2 + (native model W A k values v hv small budget).2 := by
  dsimp only [GeneralPaperEqualAddressedPreparation.run, native, run, GeneralPaperEqualBitPreparationLedger.total,
    GeneralPaperEqualNativeSampler.rounded]
  omega

theorem native_join_work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let raw := GeneralPaperValueRoundingPaperContract.run true model W 128 k values
    let lengths := GeneralPaperEqualLengthArray.run model A raw.1.1 raw.1.2
    raw.2 + lengths.2 + (native model W A k values v hv small budget).2 ≤
      GeneralPaperEqualBitPreparationLedger.profile model W A k values (rationalWordWidth budget) := by
  dsimp only
  rw [← price_join]
  exact GeneralPaperEqualBitPreparationLedger.bit_work model W A k values v hv small budget

end Blotto.GeneralPaperEqualBitContinuation
