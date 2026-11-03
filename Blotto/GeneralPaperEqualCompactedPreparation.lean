import Blotto.GeneralPaperEqualCompactedCost
import Blotto.GeneralPaperEqualRoutedPreparation

/-! One actual native preparation path through rounding, lengths, packing,
routes, full segments, positive compaction and cached integers. The record
retains separate measured prices; Boolean/width/closure work is still open. -/
namespace Blotto.GeneralPaperEqualCompactedPreparation
open MeasureTheory
open GeneralPaperEqualNativeSampler (rounded segmentHeight)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperEqualPreparedCache (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 1400000

structure Work where
  rounding : ℕ
  lengths : ℕ
  packing : ℕ
  routes : ℕ
  segments : ℕ
  compaction : ℕ
  integerProduct : ℕ
  integerCounts : ℕ
  midpointPower : ℕ

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    Prepared (terminal (rounded bits model W k values v hv) small).partition
      (lottery (rounded bits model W k values v hv) small) × Work :=
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
  let cache := GeneralPaperEqualCompactedCache.run routes.1 full.1 model A (k + 5) budget
  (cache.1, ⟨raw.2, lengths.2, packed.2, routes.2, full.2,
    cache.2.1, cache.2.2.1, cache.2.2.2.1, cache.2.2.2.2⟩)

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).1 =
      GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget := by
  unfold run
  dsimp only
  exact GeneralPaperEqualCompactedCache.data _ _ model A (k + 5) budget

theorem previous {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let result := run bits model W A k values v hv small budget
    (result.1, (result.2.rounding, result.2.lengths, result.2.packing, result.2.routes)) =
      ((GeneralPaperEqualRoutedPreparation.run bits model W A k values v hv small budget).1.prepared,
        (GeneralPaperEqualRoutedPreparation.run bits model W A k values v hv small budget).2) := by
  dsimp only
  apply Prod.ext
  · rw [data, GeneralPaperEqualRoutedPreparation.data]
    rfl
  · rfl

theorem segment_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).2.segments ≤
      4294967296 * (model.rat (4194304 * (binaryWordWidth n + k + 10)) + A + 1) := by
  have h : ∀ p : RationalTerminalPacking (terminal (rounded bits model W k values v hv) small),
      (GeneralPaperEqualNativeSegmentPreparation.prepared (rounded bits model W k values v hv) small p model A).2 ≤
        4294967296 * (model.rat (4194304 * (binaryWordWidth n + k + 10)) + A + 1) := by
    intro p
    exact GeneralPaperEqualNativeSegmentPreparation.native_work bits model W A k values v hv small p
  unfold run
  dsimp only
  apply h

theorem compaction_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).2.compaction ≤
      1048576 * (model.rat (1048576 * (binaryWordWidth n + k + 10) + 1) + A + 1) := by
  have hs : 2 ≤ segmentHeight n k := by
    unfold segmentHeight expressionHeightBudget GeneralPaperEqualNativeSampler.fieldHeight
    omega
  have hHeight := GeneralPaperEqualNativeSampler.native_lottery_height bits model W k values v hv small
  have hHead := GeneralPaperPreparedSegmentCompaction.headline model A (segmentHeight n k)
  have hArg : 1 + 2 * segmentHeight n k ≤ 1048576 * (binaryWordWidth n + k + 10) + 1 := by
    have h := GeneralPaperEqualNativeCache.segment_height_bound n k
    omega
  have hRat := model.monotone hArg
  have h : ∀ (routes : PreparedGroupOutput (terminal (rounded bits model W k values v hv) small).partition)
      (full : PreparedSegmentDescriptor (lottery (rounded bits model W k values v hv) small)),
      (GeneralPaperEqualCompactedCache.run routes full model A (k + 5) budget).2.1 ≤
        1048576 * (model.rat (1048576 * (binaryWordWidth n + k + 10) + 1) + A + 1) := by
    intro routes full
    have h := GeneralPaperEqualCompactedCost.compaction routes full model A (k + 5) budget hs hHeight.1
    exact (h.trans hHead).trans (Nat.mul_le_mul_left 1048576 (by omega))
  unfold run
  dsimp only
  apply h

theorem integer_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).2.integerProduct +
      (run bits model W A k values v hv small budget).2.integerCounts ≤
      1048576 * (model.rat (3670016 * (binaryWordWidth n + k + 10) + 2) + A + 1) := by
  have hHeight := GeneralPaperEqualNativeSampler.native_lottery_height bits model W k values v hv small
  have hCount := (GeneralPaperEqualNativeCache.compact_count (rounded bits model W k values v hv) small).2
  have hHead := GeneralPaperEqualCompactedCost.integer_headline model A _ (segmentHeight n k) hCount
  have hArg : 7 * segmentHeight n k + 2 ≤ 3670016 * (binaryWordWidth n + k + 10) + 2 := by
    have h := GeneralPaperEqualNativeCache.segment_height_bound n k
    omega
  have hRat := model.monotone hArg
  have h : ∀ (routes : PreparedGroupOutput (terminal (rounded bits model W k values v hv) small).partition)
      (full : PreparedSegmentDescriptor (lottery (rounded bits model W k values v hv) small)),
      (GeneralPaperEqualCompactedCache.run routes full model A (k + 5) budget).2.2.1 +
        (GeneralPaperEqualCompactedCache.run routes full model A (k + 5) budget).2.2.2.1 ≤
        1048576 * (model.rat (3670016 * (binaryWordWidth n + k + 10) + 2) + A + 1) := by
    intro routes full
    have h := GeneralPaperEqualCompactedCost.integer routes full model A (k + 5) budget hHeight.1
    exact ((Nat.add_le_add h.1 h.2).trans hHead).trans (Nat.mul_le_mul_left 1048576 (by omega))
  unfold run
  dsimp only
  apply h

theorem power_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).2.midpointPower ≤
      64 * (binaryWordWidth (k + 5) + 1) *
        (A + model.rat (GeneralPaperNatPowerOperands.width 2 (k + 5))) + 128 * A + 128 := by
  unfold run
  dsimp only
  exact GeneralPaperEqualCompactedCost.power _ _ model A (k + 5) budget

theorem epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (small : ∀ j, 2 * (rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 < budget) (primitive : ℕ → ℕ) (address : ℕ) :
    let cache := (run bits model W A (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget).1
    let μ := GeneralPaperEqualCachedTraceLaw.outputLaw cache model primitive address
    Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (eps : ℝ) := by
  dsimp only
  rw [data]
  exact GeneralPaperEqualCachedTraceLaw.native_epsilon bits model W values v hv eps hp hOne small budget hB primitive address

end Blotto.GeneralPaperEqualCompactedPreparation
