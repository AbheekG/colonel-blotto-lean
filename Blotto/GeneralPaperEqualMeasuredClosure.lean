import Blotto.GeneralPaperStoredBooleanCache

/-! The cache/sampler now consumes measured width and Boolean constructors.
Final address construction and complete preparation lifetime remain open. -/
namespace Blotto.GeneralPaperEqualMeasuredClosure
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperPositiveSegmentCompaction (compact)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def make {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (segments : PreparedSegmentDescriptor (compact l))
    (model : RationalCostModel) (A K : ℕ) (budget : ℚ) : Prepared G l × (ℕ × ℕ × ℕ × ℕ) :=
  let integer := GeneralPaperStoredCategoricalCounts.run segments model A
  let power := GeneralPaperNatPowerBits.run model.rat A 2 K
  let width := GeneralPaperStoredRejectionWidth.run model A integer.1.D
  let hD : 0 < integer.1.D := by
    rw [integer.1.D_correct]
    exact GeneralPaperEqualCategoricalIntegerData.denominator_pos segments.lottery.weight
  let actual : Prepared G l :=
    ⟨routes, segments, integer.1.D, integer.1.D_correct, integer.1.counts, integer.1.counts_correct,
      width.1, GeneralPaperStoredRejectionWidth.data model A integer.1.D hD,
      K, power.1.power, (by rw [GeneralPaperNatPowerBits.data]; exact (GeneralPaperNatPower.data 2 K).1), budget⟩
  (actual, (integer.2.1, integer.2.2, power.2 + 128 * A + 128, width.2))

theorem make_data {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (segments : PreparedSegmentDescriptor (compact l))
    (model : RationalCostModel) (A K : ℕ) (budget : ℚ) :
    (make routes segments model A K budget).1 = GeneralPaperEqualPreparedCache.prepare G l K budget :=
  GeneralPaperEqualCompactedCache.unique _ _ rfl rfl

structure Work where
  compaction : ℕ
  integerProduct : ℕ
  integerCounts : ℕ
  midpointPower : ℕ
  rejectionWidth : ℕ
  booleanCache : ℕ

theorem canonical_close {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Prepared G l) (k : ℕ) (hk : p.midpointBits = k + 5) (address : ℕ)
    (ha : address = GeneralPaperEqualBitDrawRates.address n m k (rationalWordWidth p.budget)) :
    (⟨p, GeneralPaperEqualBooleanCache.prepare p, k, hk, address, ha⟩ : GeneralPaperEqualStoredBitSampler.Sampler G l) =
      GeneralPaperEqualStoredBitSampler.prepare p k hk := by
  cases ha
  rfl

def run {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (groupSize : ℕ) (hGroupSize : groupSize = m)
    (model : RationalCostModel) (A k : ℕ) (budget : ℚ) : GeneralPaperEqualStoredBitSampler.Sampler G l × Work :=
  let compacted := GeneralPaperPreparedSegmentCompaction.run full model A
  let actual := make routes compacted.1 model A (k + 5) budget
  let boolean := GeneralPaperStoredBooleanCache.run actual.1 model A
  let address := GeneralPaperEqualBitDrawRates.address routes.table.data.size groupSize k (rationalWordWidth budget)
  let sampler : GeneralPaperEqualStoredBitSampler.Sampler G l :=
    ⟨actual.1, boolean.1, k, rfl, address, (by dsimp only [address]; rw [routes.table.size, hGroupSize]; rfl)⟩
  (sampler, ⟨compacted.2, actual.2.1, actual.2.2.1, actual.2.2.2.1, actual.2.2.2.2, boolean.2⟩)

theorem data {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (groupSize : ℕ) (hGroupSize : groupSize = m)
    (model : RationalCostModel) (A k : ℕ) (budget : ℚ) :
    (run routes full groupSize hGroupSize model A k budget).1 =
      GeneralPaperEqualStoredBitSampler.prepare (GeneralPaperEqualPreparedCache.prepare G l (k + 5) budget) k rfl := by
  unfold run
  dsimp only
  rw [GeneralPaperStoredBooleanCache.data]
  have h := make_data routes (GeneralPaperPreparedSegmentCompaction.run full model A).1 model A (k + 5) budget
  apply Eq.trans (canonical_close _ _ rfl _ _)
  exact GeneralPaperEqualCachedPreparation.sampler_eq _ _ k rfl rfl h

theorem previous_prices {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (groupSize : ℕ) (hGroupSize : groupSize = m)
    (model : RationalCostModel) (A k : ℕ) (budget : ℚ) :
    let result := (run routes full groupSize hGroupSize model A k budget).2
    (result.compaction, result.integerProduct, result.integerCounts, result.midpointPower) =
      (GeneralPaperEqualCompactedCache.run routes full model A (k + 5) budget).2 := rfl

theorem width_work {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (groupSize : ℕ) (hGroupSize : groupSize = m)
    (model : RationalCostModel) (A k : ℕ) (budget : ℚ) (L : ℕ)
    (hD : binaryWordWidth (GeneralPaperEqualPreparedCache.prepare G l (k + 5) budget).D ≤ L) :
    (run routes full groupSize hGroupSize model A k budget).2.rejectionWidth ≤
      128 * (L + 1) * (A + model.rat (L + 6) + 1) := by
  have h := make_data routes (GeneralPaperPreparedSegmentCompaction.run full model A).1 model A (k + 5) budget
  have hWord : binaryWordWidth (make routes (GeneralPaperPreparedSegmentCompaction.run full model A).1 model A (k + 5) budget).1.D ≤ L := by
    rw [h]
    exact hD
  exact GeneralPaperStoredRejectionWidth.word_work model A _ L hWord

theorem boolean_work {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (groupSize : ℕ) (hGroupSize : groupSize = m)
    (model : RationalCostModel) (A k : ℕ) (budget : ℚ) (L : ℕ)
    (hD : binaryWordWidth (GeneralPaperEqualPreparedCache.prepare G l (k + 5) budget).D ≤ L) :
    (run routes full groupSize hGroupSize model A k budget).2.booleanCache ≤
      GeneralPaperStoredBooleanCache.bound model A (GeneralPaperPositiveSegmentCompaction.count l)
        (GeneralPaperEqualPreparedCache.prepare G l (k + 5) budget).rangeBits L := by
  have h := make_data routes (GeneralPaperPreparedSegmentCompaction.run full model A).1 model A (k + 5) budget
  have hWork := GeneralPaperStoredBooleanCache.work
    (make routes (GeneralPaperPreparedSegmentCompaction.run full model A).1 model A (k + 5) budget).1 model A L
    (by rw [h]; exact hD)
  rw [h] at hWork
  unfold run
  dsimp only
  rw [h]
  exact hWork

end Blotto.GeneralPaperEqualMeasuredClosure
