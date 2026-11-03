import Blotto.GeneralPaperEqualFirstSegmentCallerSpace

/-! Actual positive compaction and categorical integer construction for the
corrected source. Full/compact arrays and their executed prices remain owned
beside the proved source caller. Every recursion and callback cursor is covered. -/
namespace Blotto.GeneralPaperEqualFirstIntegerCallerSpace
open GeneralPaperEqualFirstNativeFacts (rounded segmentHeight)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (count)
open GeneralPaperEqualFirstSegmentCallerSpace (full)
open GeneralPaperEqualRetainedStorage (segmentFoot segmentProfile)
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def compacted {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) :=
  GeneralPaperPreparedSegmentCompaction.run (full model W A k values v hv small).1 model A

def actual {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) :=
  GeneralPaperStoredCategoricalCounts.run (compacted model W A k values v hv small).1 model A

def compactionPrice (model : RationalCostModel) (A n k : ℕ) : ℕ :=
  GeneralPaperPreparedSegmentCompaction.bound model A 9 (segmentHeight n k)

theorem compaction_work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) :
    (compacted model W A k values v hv small).2 ≤ compactionPrice model A n k := by
  have hs : 2 ≤ segmentHeight n k := by
    unfold segmentHeight GeneralPaperEqualFirstNativeFacts.fieldHeight expressionHeightBudget
    omega
  exact GeneralPaperPreparedSegmentCompaction.work (full model W A k values v hv small).1 model A hs
    (GeneralPaperEqualFirstNativeFacts.native_lottery_height true model W k values v hv small).1

def resident {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFirstSegmentCallerSpace.borrowed model W A k values v hv small budget+
    segmentFoot A (full model W A k values v hv small).1+
    segmentFoot A (compacted model W A k values v hv small).1+
    fields A [(full model W A k values v hv small).2,(compacted model W A k values v hv small).2]+256*A

def residentProfile {n : ℕ} (model : RationalCostModel) (W A k m : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFirstSegmentCallerSpace.ownerProfile model W A k m values budget+
    segmentProfile A 3 9 (segmentHeight n k)+segmentProfile A 3 7 (segmentHeight n k)+
    2*(natBits (GeneralPaperEqualFirstPrefixRates.segmentBound model A n k+compactionPrice model A n k)+A)+288*A

theorem resident_bound {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    resident model W A k values v hv small budget ≤
      residentProfile model W A k (terminal (rounded true model W k values v hv) small).groups.length values budget := by
  have hCaller := GeneralPaperEqualFirstSegmentCallerSpace.owner_bound model W A k values v hv small budget
  have hHeight := GeneralPaperEqualFirstNativeFacts.native_lottery_height true model W k values v hv small
  have hm := GeneralPaperEqualFirstNativeCache.group_count (rounded true model W k values v hv) small
  have hc := (GeneralPaperEqualFirstNativeCache.compact_count (rounded true model W k values v hv) small).2
  have hFull := (GeneralPaperEqualRetainedStorage.segment_bound A (full model W A k values v hv small).1 hHeight).trans
    (GeneralPaperEqualNativeRetainedStorage.segmentProfile_mono A hm le_rfl le_rfl)
  have hCompact := (GeneralPaperEqualRetainedStorage.segment_bound A (compacted model W A k values v hv small).1
    (GeneralPaperPositiveSegmentCompaction.compact_height _ hHeight)).trans
      (GeneralPaperEqualNativeRetainedStorage.segmentProfile_mono A hm hc le_rfl)
  have hp := GeneralPaperEqualFirstSegmentCallerSpace.full_work model W A k values v hv small
  have hq := compaction_work model W A k values v hv small
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A
    (GeneralPaperEqualFirstPrefixRates.segmentBound model A n k+compactionPrice model A n k)
    [(full model W A k values v hv small).2,(compacted model W A k values v hv small).2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> omega)
  change fields A _ ≤ 2*(natBits (GeneralPaperEqualFirstPrefixRates.segmentBound model A n k+compactionPrice model A n k)+A)+32*A at hFields
  unfold resident residentProfile
  exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hCaller hFull) hCompact) hFields) (256*A)).trans_eq (by ring)

def compactionBorrowed {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFirstSegmentCallerSpace.borrowed model W A k values v hv small budget+
    segmentFoot A (full model W A k values v hv small).1+natBits (full model W A k values v hv small).2+128*A

theorem compaction_borrowed_bound {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    compactionBorrowed model W A k values v hv small budget ≤
      residentProfile model W A k (terminal (rounded true model W k values v hv) small).groups.length values budget :=
  (GeneralPaperEqualCompactionCallerLifetime.pre_owner_le A
    (GeneralPaperEqualFirstSegmentCallerSpace.borrowed model W A k values v hv small budget)
    (segmentFoot A (full model W A k values v hv small).1) (segmentFoot A (compacted model W A k values v hv small).1)
    (full model W A k values v hv small).2 (compacted model W A k values v hv small).2).trans
      (resident_bound model W A k values v hv small budget)

def compactionWindow {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperCompactionLifetime.Phase (count (lottery (rounded true model W k values v hv) small))) : ℕ :=
  GeneralPaperCompactionLifetime.window (full model W A k values v hv small).1 model A
    (compactionBorrowed model W A k values v hv small budget) phase

def compactionProfile {n : ℕ} (model : RationalCostModel) (W A k m c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperCompactionLifetime.profile model A c 9 (segmentHeight n k) (residentProfile model W A k m values budget)

theorem compaction_phases {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperCompactionLifetime.Phase (count (lottery (rounded true model W k values v hv) small))) :
    compactionWindow model W A k values v hv small budget phase ≤
      compactionProfile model W A k (terminal (rounded true model W k values v hv) small).groups.length
        (count (lottery (rounded true model W k values v hv) small)) values budget := by
  have hs : 2 ≤ segmentHeight n k := by
    unfold segmentHeight GeneralPaperEqualFirstNativeFacts.fieldHeight expressionHeightBudget
    omega
  have h := GeneralPaperCompactionLifetime.all_phases (full model W A k values v hv small).1 model A
    (compactionBorrowed model W A k values v hv small budget) hs
    (GeneralPaperEqualFirstNativeFacts.native_lottery_height true model W k values v hv small).1 phase
  exact h.trans (GeneralPaperCompactionLifetime.borrowed_mono model A _ _ _ _ _
    (compaction_borrowed_bound model W A k values v hv small budget))

def window {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperCategoricalIntegerLifetime.Phase (count (lottery (rounded true model W k values v hv) small))) : ℕ :=
  GeneralPaperCategoricalIntegerLifetime.window (compacted model W A k values v hv small).1 model A
    (resident model W A k values v hv small budget) phase

def profile {n : ℕ} (model : RationalCostModel) (W A k m c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperCategoricalIntegerLifetime.profile model A c (segmentHeight n k) (residentProfile model W A k m values budget)

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperCategoricalIntegerLifetime.Phase (count (lottery (rounded true model W k values v hv) small))) :
    window model W A k values v hv small budget phase ≤ profile model W A k
      (terminal (rounded true model W k values v hv) small).groups.length
      (count (lottery (rounded true model W k values v hv) small)) values budget := by
  let p := (compacted model W A k values v hv small).1
  have hl := GeneralPaperPositiveSegmentCompaction.compact_height
    (lottery (rounded true model W k values v hv) small)
    (GeneralPaperEqualFirstNativeFacts.native_lottery_height true model W k values v hv small)
  have hWeights : ∀ i, RationalHeight (p.weights.read i) (segmentHeight n k) := by
    intro i; rw [p.weight_correct]; exact hl.1 i
  have h := GeneralPaperCategoricalIntegerLifetime.all_phases p model A hWeights
    (resident model W A k values v hv small budget) phase
  exact h.trans (GeneralPaperCategoricalIntegerLifetime.borrowed_mono model A _ _ _ _
    (resident_bound model W A k values v hv small budget))

end Blotto.GeneralPaperEqualFirstIntegerCallerSpace
