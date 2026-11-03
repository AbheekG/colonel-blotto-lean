import Blotto.GeneralPaperEqualFirstNativeFacts

/-! The compact prepared cache instantiated at the native positive-rounded
paper inputs. The seven-segment and short-word bounds are derived from
the actual producer, not supplied as assumptions about returned tables. -/
namespace Blotto.GeneralPaperEqualFirstNativeCache
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
open GeneralPaperEqualFirstNativeFacts (rounded roundDen segmentHeight)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (compact count)
open GeneralPaperEqualPreparedCache (Prepared)

def prepare {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :=
  GeneralPaperEqualPreparedCache.prepare (terminal (rounded bits model W k values v hv) small).partition
    (lottery (rounded bits model W k values v hv) small) (k + 5) budget

theorem compact_count {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) :
    0 < count (lottery v small) ∧ count (lottery v small) ≤ 7 := by
  refine ⟨GeneralPaperPositiveSegmentCompaction.count_positive _, ?_⟩
  rw [GeneralPaperPositiveSegmentCompaction.count_card]
  exact GeneralPaperEqualFiniteKernel.positive_segments v small

theorem group_count {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) :
    (terminal v small).groups.length ≤ 3 := by
  rcases (terminal v small).groups_count with h | h <;> omega

theorem route_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) (j : Fin n) :
    RationalHeight ((prepare bits model W k values v hv small budget).routes.table.read j).2
      (binaryWordWidth n + k + 10) := by
  let i := terminal (rounded bits model W k values v hv) small
  let D := roundDen bits model W k values
  have hL : ∀ j, OnRationalLattice D (i.partition.length j) := fun j =>
    (GeneralPaperEqualFirstNativeFacts.rounded_lattice bits model W k values v hv j).int_mul 2
  exact ((prepare bits model W k values v hv small budget).routes.coefficient_height_lattice D
    (GeneralPaperEqualFirstNativeFacts.roundDen_positive bits model W k values v hv) hL
    small i.partition_total_le j).mono (GeneralPaperEqualFirstNativeFacts.roundDen_word bits model W k values v hv)

theorem descriptor_cells {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (prepare bits model W k values v hv small budget).segments.rationalCells ≤ 49 :=
  GeneralPaperEqualPreparedCache.descriptor_cells _ (group_count _ _) (compact_count _ _).2

theorem descriptor_payload {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (prepare bits model W k values v hv small budget).segments.payloadBitCost ≤
      49 * (1 + 2 * segmentHeight n k) :=
  GeneralPaperEqualPreparedCache.descriptor_payload _ (group_count _ _) (compact_count _ _).2
    (GeneralPaperEqualFirstNativeFacts.native_lottery_height bits model W k values v hv small)

theorem segment_height_bound (n k : ℕ) : segmentHeight n k ≤ 524288 * (binaryWordWidth n + k + 11) := by
  unfold segmentHeight expressionHeightBudget GeneralPaperEqualFirstNativeFacts.fieldHeight
  norm_num
  omega

theorem denominator_word {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    binaryWordWidth (prepare bits model W k values v hv small budget).D ≤
      3670016 * (binaryWordWidth n + k + 11) + 1 := by
  have h := GeneralPaperEqualPreparedCache.denominator_word
    (prepare bits model W k values v hv small budget)
    (GeneralPaperEqualFirstNativeFacts.native_lottery_height bits model W k values v hv small)
  have hc := Nat.mul_le_mul_left (segmentHeight n k) (compact_count (rounded bits model W k values v hv) small).2
  have hs := segment_height_bound n k
  nlinarith only [h, hc, hs]

theorem rangeBits {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (prepare bits model W k values v hv small budget).rangeBits ≤
      3670016 * (binaryWordWidth n + k + 11) + 1 := by
  have h := GeneralPaperEqualPreparedCache.rangeBits_bound
    (prepare bits model W k values v hv small budget)
    (GeneralPaperEqualFirstNativeFacts.native_lottery_height bits model W k values v hv small)
  have hc := Nat.mul_le_mul_left (segmentHeight n k) (compact_count (rounded bits model W k values v hv) small).2
  have hs := segment_height_bound n k
  nlinarith only [h, hc, hs]

theorem count_word {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (j : Fin (count (lottery (rounded bits model W k values v hv) small))) :
    binaryWordWidth ((prepare bits model W k values v hv small budget).counts.read j) ≤
      3670016 * (binaryWordWidth n + k + 11) + 1 :=
  (binaryWordWidth_mono (GeneralPaperEqualPreparedCache.counts_bounded _ j)).trans
    (denominator_word bits model W k values v hv small budget)

end Blotto.GeneralPaperEqualFirstNativeCache
