import Blotto.GeneralPaperCategoricalIntegerLifetime

/-! The integer-data kernel consumes the actual measured compact descriptor.
Its caller retains the previously bounded native prefix, full and compact
descriptors and both return-price records. All source projections agree with
the actual returned sampler's preparation; these are erased observers. -/
namespace Blotto.GeneralPaperEqualIntegerCallerLifetime
open GeneralPaperEqualNativeSampler (rounded segmentHeight)
open GeneralPaperEqualFiniteKernel (lottery terminal)
open GeneralPaperPositiveSegmentCompaction (count compact)
open GeneralPaperEqualRetainedStorage (segmentFoot segmentProfile)
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def full {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :=
  GeneralPaperEqualSegmentCallerLifetime.segmentReturn bits model W A exponent values v hv small budget

def compacted {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :=
  GeneralPaperPreparedSegmentCompaction.run (full bits model W A exponent values v hv small budget).1 model A

def actual {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :=
  GeneralPaperStoredCategoricalCounts.run (compacted bits model W A exponent values v hv small budget).1 model A

theorem source_prices {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    let w := (GeneralPaperEqualAddressedPreparation.run bits model W A exponent values v hv small budget).2.1.1
    (actual bits model W A exponent values v hv small budget).2 = (w.integerProduct, w.integerCounts)  := by
  simp only [actual, compacted, full, GeneralPaperEqualSegmentCallerLifetime.segmentReturn,
    GeneralPaperEqualAddressedPreparation.run, GeneralPaperEqualAddressedClosure.run,
    GeneralPaperEqualMeasuredClosure.make]

theorem source_compaction_price {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    let w := (GeneralPaperEqualAddressedPreparation.run bits model W A exponent values v hv small budget).2.1.1
    (compacted bits model W A exponent values v hv small budget).2 = w.compaction  := by
  simp only [compacted, full, GeneralPaperEqualSegmentCallerLifetime.segmentReturn,
    GeneralPaperEqualAddressedPreparation.run, GeneralPaperEqualAddressedClosure.run]

def resident {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperEqualSegmentCallerLifetime.borrowed bits model W A exponent values v hv small budget +
    segmentFoot A (full bits model W A exponent values v hv small budget).1 +
    segmentFoot A (compacted bits model W A exponent values v hv small budget).1 +
    fields A [(full bits model W A exponent values v hv small budget).2,
      (compacted bits model W A exponent values v hv small budget).2] + 256 * A

def residentProfile {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualSegmentCallerLifetime.ownerProfile model W A exponent values budget +
    segmentProfile A 3 9 (segmentHeight n exponent) + segmentProfile A 3 7 (segmentHeight n exponent) +
    2 * (natBits (GeneralPaperEqualBitPreparationLedger.profile model W A exponent values (rationalWordWidth budget)) + A) + 288 * A

theorem segment_compaction_price (w : GeneralPaperEqualCompactedPreparation.Work) (width boolean budget address controls : ℕ) :
    w.segments + w.compaction ≤ GeneralPaperEqualBitPreparationLedger.total w width boolean budget address controls := by
  unfold GeneralPaperEqualBitPreparationLedger.total
  omega

theorem resident_bound {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    resident true model W A exponent values v hv small budget ≤ residentProfile model W A exponent values budget := by
  have hCaller := GeneralPaperEqualSegmentCallerLifetime.owner_bound model W A exponent values v hv small budget
  have hHeight := GeneralPaperEqualNativeSampler.native_lottery_height true model W exponent values v hv small
  have hGroups := GeneralPaperEqualNativeCache.group_count (rounded true model W exponent values v hv) small
  have hCount := (GeneralPaperEqualNativeCache.compact_count (rounded true model W exponent values v hv) small).2
  have hFull := (GeneralPaperEqualRetainedStorage.segment_bound A
    (full true model W A exponent values v hv small budget).1 hHeight).trans
      (GeneralPaperEqualNativeRetainedStorage.segmentProfile_mono A hGroups le_rfl le_rfl)
  have hCompact := (GeneralPaperEqualRetainedStorage.segment_bound A
    (compacted true model W A exponent values v hv small budget).1
    (GeneralPaperPositiveSegmentCompaction.compact_height _ hHeight)).trans
      (GeneralPaperEqualNativeRetainedStorage.segmentProfile_mono A hGroups hCount le_rfl)
  let result := (GeneralPaperEqualAddressedPreparation.run true model W A exponent values v hv small budget).2
  have hCost := GeneralPaperEqualBitPreparationLedger.bit_work model W A exponent values v hv small budget
  have hPrice := (segment_compaction_price result.1.1 result.1.2.1 result.1.2.2 result.2.1 result.2.2.1 result.2.2.2).trans hCost
  have hFullPrice := GeneralPaperEqualSegmentCallerLifetime.source_price true model W A exponent values v hv small budget
  change (full true model W A exponent values v hv small budget).2 = _ at hFullPrice
  have hCompactPrice := source_compaction_price true model W A exponent values v hv small budget
  rw [← hFullPrice, ← hCompactPrice] at hPrice
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A
    (GeneralPaperEqualBitPreparationLedger.profile model W A exponent values (rationalWordWidth budget))
    [(full true model W A exponent values v hv small budget).2,
      (compacted true model W A exponent values v hv small budget).2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (Nat.le_add_right _ _).trans hPrice
      · exact (Nat.le_add_left _ _).trans hPrice)
  change fields A _ ≤ 2 * (natBits (GeneralPaperEqualBitPreparationLedger.profile model W A exponent values (rationalWordWidth budget)) + A) + 32 * A at hFields
  unfold resident residentProfile
  have hSum := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hCaller hFull) hCompact) hFields) (256 * A)
  exact hSum.trans_eq (by ring)

def window {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperCategoricalIntegerLifetime.Phase (count (lottery (rounded bits model W exponent values v hv) small))) : ℕ :=
  GeneralPaperCategoricalIntegerLifetime.window (compacted bits model W A exponent values v hv small budget).1 model A
    (resident bits model W A exponent values v hv small budget) phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ)
    (budget : ℚ) (c : ℕ) : ℕ :=
  GeneralPaperCategoricalIntegerLifetime.profile model A c (segmentHeight n exponent)
    (residentProfile model W A exponent values budget)

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperCategoricalIntegerLifetime.Phase (count (lottery (rounded true model W exponent values v hv) small))) :
    window true model W A exponent values v hv small budget phase ≤
      profile model W A exponent values budget (count (lottery (rounded true model W exponent values v hv) small)) := by
  let p := (compacted true model W A exponent values v hv small budget).1
  have hHeight := GeneralPaperPositiveSegmentCompaction.compact_height
    (lottery (rounded true model W exponent values v hv) small)
    (GeneralPaperEqualNativeSampler.native_lottery_height true model W exponent values v hv small)
  have hWeights : ∀ i, RationalHeight (p.weights.read i) (segmentHeight n exponent) := by
    intro i
    rw [p.weight_correct]
    exact hHeight.1 i
  have hKernel := GeneralPaperCategoricalIntegerLifetime.all_phases p model A hWeights
    (resident true model W A exponent values v hv small budget) phase
  have hResident := resident_bound model W A exponent values v hv small budget
  exact hKernel.trans (GeneralPaperCategoricalIntegerLifetime.borrowed_mono model A _ _ _ _ hResident)

end Blotto.GeneralPaperEqualIntegerCallerLifetime
