import Blotto.GeneralPaperEqualCachedEmission

/-! The compact prepared cache instantiated at the native positive-rounded
paper inputs. The seven-segment and short-word bounds are derived from
the actual producer, not supplied as assumptions about returned tables. -/
namespace Blotto.GeneralPaperEqualNativeCache
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
open GeneralPaperEqualNativeSampler (rounded roundDen segmentHeight)
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
      (binaryWordWidth n + k + 9) := by
  let i := terminal (rounded bits model W k values v hv) small
  let D := roundDen bits model W k values
  have hL : ∀ j, OnRationalLattice D (i.partition.length j) := fun j =>
    (GeneralPaperEqualNativeSampler.rounded_lattice bits model W k values v hv j).int_mul 2
  exact ((prepare bits model W k values v hv small budget).routes.coefficient_height_lattice D
    (GeneralPaperEqualNativeSampler.roundDen_positive bits model W k values v hv) hL
    small i.partition_total_le j).mono (GeneralPaperEqualNativeSampler.roundDen_word bits model W k values v hv)

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
    (GeneralPaperEqualNativeSampler.native_lottery_height bits model W k values v hv small)

theorem segment_height_bound (n k : ℕ) : segmentHeight n k ≤ 524288 * (binaryWordWidth n + k + 10) := by
  unfold segmentHeight expressionHeightBudget GeneralPaperEqualNativeSampler.fieldHeight
  norm_num
  omega

theorem denominator_word {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    binaryWordWidth (prepare bits model W k values v hv small budget).D ≤
      3670016 * (binaryWordWidth n + k + 10) + 1 := by
  have h := GeneralPaperEqualPreparedCache.denominator_word
    (prepare bits model W k values v hv small budget)
    (GeneralPaperEqualNativeSampler.native_lottery_height bits model W k values v hv small)
  have hc := Nat.mul_le_mul_left (segmentHeight n k) (compact_count (rounded bits model W k values v hv) small).2
  have hs := segment_height_bound n k
  nlinarith only [h, hc, hs]

theorem rangeBits {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (prepare bits model W k values v hv small budget).rangeBits ≤
      3670016 * (binaryWordWidth n + k + 10) + 1 := by
  have h := GeneralPaperEqualPreparedCache.rangeBits_bound
    (prepare bits model W k values v hv small budget)
    (GeneralPaperEqualNativeSampler.native_lottery_height bits model W k values v hv small)
  have hc := Nat.mul_le_mul_left (segmentHeight n k) (compact_count (rounded bits model W k values v hv) small).2
  have hs := segment_height_bound n k
  nlinarith only [h, hc, hs]

theorem count_word {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (j : Fin (count (lottery (rounded bits model W k values v hv) small))) :
    binaryWordWidth ((prepare bits model W k values v hv small budget).counts.read j) ≤
      3670016 * (binaryWordWidth n + k + 10) + 1 :=
  (binaryWordWidth_mono (GeneralPaperEqualPreparedCache.counts_bounded _ j)).trans
    (denominator_word bits model W k values v hv small budget)

theorem output_fullBudget {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 ≤ budget) (primitive : ℕ → ℕ) (A : ℕ)
    (slot : Fin (count (lottery (rounded bits model W k values v hv) small))) (fresh : Fin (k + 5) → Bool) :
    FullBudget (budget : ℝ)
      (GeneralPaperEqualCachedEmission.emit (prepare bits model W k values v hv small budget)
        model primitive A slot fresh).1.realAllocation :=
  GeneralPaperEqualCachedEmission.emit_fullBudget _ _ _ _ hB (GeneralPaperEqualFiniteKernel.endpoints _ _) _ _

def outputHeight (n k b : ℕ) : ℕ :=
  expressionHeightBudget (max (binaryWordWidth n + k + 9)
    (GeneralPaperEqualCachedEmission.scaledHeight (segmentHeight n k) (k + 5) b)) 1

theorem outputHeight_bound (n k b : ℕ) :
    outputHeight n k b ≤ 33554432 * (b + binaryWordWidth n + k + 10) := by
  let X := binaryWordWidth n + k + 10
  have hs : segmentHeight n k ≤ 524288 * X := segment_height_bound n k
  have hmax : max (segmentHeight n k) (k + 5 + 2) ≤ segmentHeight n k + k + 7 :=
    max_le (by omega) (by omega)
  have hg : GeneralPaperEqualCachedEmission.groupHeight (segmentHeight n k) (k + 5) ≤ 4194368 * X := by
    unfold GeneralPaperEqualCachedEmission.groupHeight expressionHeightBudget
    norm_num
    dsimp only [X] at hs ⊢
    omega
  have hm : max b (GeneralPaperEqualCachedEmission.groupHeight (segmentHeight n k) (k + 5)) ≤
      b + GeneralPaperEqualCachedEmission.groupHeight (segmentHeight n k) (k + 5) := max_le (by omega) (by omega)
  have hb : GeneralPaperEqualCachedEmission.scaledHeight (segmentHeight n k) (k + 5) b ≤ 2 * b + 8388736 * X + 1 := by
    unfold GeneralPaperEqualCachedEmission.scaledHeight expressionHeightBudget
    norm_num
    omega
  have hm' : max (binaryWordWidth n + k + 9)
      (GeneralPaperEqualCachedEmission.scaledHeight (segmentHeight n k) (k + 5) b) ≤
      binaryWordWidth n + k + 9 + GeneralPaperEqualCachedEmission.scaledHeight (segmentHeight n k) (k + 5) b :=
    max_le (by omega) (by omega)
  unfold outputHeight expressionHeightBudget
  norm_num
  dsimp only [X] at hb
  omega

theorem output_height {n b : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : RationalHeight budget b) (primitive : ℕ → ℕ) (A : ℕ)
    (slot : Fin (count (lottery (rounded bits model W k values v hv) small)))
    (fresh : Fin (k + 5) → Bool) (j : Fin n) :
    RationalHeight ((GeneralPaperEqualCachedEmission.emit (prepare bits model W k values v hv small budget)
      model primitive A slot fresh).1.allocation j) (33554432 * (b + binaryWordWidth n + k + 10)) := by
  have hs : 2 ≤ segmentHeight n k := by
    unfold segmentHeight expressionHeightBudget GeneralPaperEqualNativeSampler.fieldHeight
    norm_num
    omega
  have h := GeneralPaperEqualCachedEmission.emit_height
    (prepare bits model W k values v hv small budget) model primitive A hs
    (GeneralPaperEqualNativeSampler.native_lottery_height bits model W k values v hv small) hB
    (by omega : 1 ≤ binaryWordWidth n + k + 9) (route_height bits model W k values v hv small budget) slot fresh j
  exact h.mono (outputHeight_bound n k b)

end Blotto.GeneralPaperEqualNativeCache
