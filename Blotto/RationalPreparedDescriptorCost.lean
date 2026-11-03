import Blotto.PreparedSegmentDescriptorHeight
import Blotto.RationalDescriptorBitCost
import Blotto.RationalOverlapHeight

/-! The primary counted descriptor compilers now materialize their tables.
Formula work and written rational payload have explicit bounds. Parent/input
construction, address/metadata, allocation and physical backend remain separate. -/

namespace Blotto.RationalThreeGeometryCode
open scoped BigOperators

theorem compiledLotteryReference_height (g : RationalThreeGeometry) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    (compiledLotteryReference g).HeightAt (expressionHeightBudget s 16) := by
  constructor
  · intro slot
    change RationalHeight ((chosen slot).value (environment g)) _
    rw [chosen_value]
    exact chosen_height g slot s hs hEnv
  · intro slot j
    change RationalHeight ((vertex (RationalThreeGeometry.edges slot).1 j).value (environment g)) _ ∧
      RationalHeight ((vertex (RationalThreeGeometry.edges slot).2 j).value (environment g)) _
    rw [vertex_value, vertex_value]
    exact ⟨(vertex_height g _ j s hs hEnv).mono (expressionHeightBudget_mono s (by decide : 2 ≤ 16)),
      (vertex_height g _ j s hs hEnv).mono (expressionHeightBudget_mono s (by decide : 2 ≤ 16))⟩

noncomputable def preparedDescriptorBitCost (model : RationalCostModel) (g : RationalThreeGeometry) : ℕ :=
  descriptorBitCost model g + (PreparedSegmentDescriptor.prepare (compiledLotteryReference g)).payloadBitCost

theorem preparedDescriptorBitCost_bound (model : RationalCostModel) (g : RationalThreeGeometry)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    preparedDescriptorBitCost model g ≤ 2799 * model.rat (1 + 2 * expressionHeightBudget s 16) := by
  have hFormula := descriptorBitCost_bound model g s hs hEnv
  have hPayload := (PreparedSegmentDescriptor.prepare (compiledLotteryReference g)).payloadBitCost_bound
    _ (compiledLotteryReference_height g s hs hEnv)
  have hCopies : (PreparedSegmentDescriptor.prepare (compiledLotteryReference g)).payloadBitCost ≤
      63 * model.rat (1 + 2 * expressionHeightBudget s 16) := by
    exact hPayload.trans (Nat.mul_le_mul_left 63 (model.word_le _))
  unfold preparedDescriptorBitCost
  omega

def preparedDescriptorArithmeticWork (g : RationalThreeGeometry) : ℕ :=
  (∑ slot : Fin 9, ((chosen slot).run (environment g)).2) +
    (∑ slot : Fin 9, ∑ j : Fin 3, ((vertex (RationalThreeGeometry.edges slot).1 j).run (environment g)).2) +
    (∑ slot : Fin 9, ∑ j : Fin 3, ((vertex (RationalThreeGeometry.edges slot).2 j).run (environment g)).2)

theorem preparedDescriptorArithmeticWork_bound (g : RationalThreeGeometry) : preparedDescriptorArithmeticWork g ≤ 2736 := by
  have hw : (∑ slot : Fin 9, ((chosen slot).run (environment g)).2) ≤ 9 * 256 := by
    calc
      _ ≤ ∑ _slot : Fin 9, 256 := Finset.sum_le_sum (fun slot _ => chosen_operations g slot)
      _ = _ := by simp
  have hp : (∑ slot : Fin 9, ∑ j : Fin 3, ((vertex (RationalThreeGeometry.edges slot).1 j).run (environment g)).2) ≤ 9 * (3 * 8) := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 3, 8 := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => vertex_operations g _ j))
      _ = _ := by simp
  have hq : (∑ slot : Fin 9, ∑ j : Fin 3, ((vertex (RationalThreeGeometry.edges slot).2 j).run (environment g)).2) ≤ 9 * (3 * 8) := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 3, 8 := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => vertex_operations g _ j))
      _ = _ := by simp
  unfold preparedDescriptorArithmeticWork
  omega

end Blotto.RationalThreeGeometryCode
namespace Blotto.RationalOverlapFormula

theorem descriptorReference_eq {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) : descriptorReference G B = G.descriptor B := by
  have he := descriptor_eq G B
  simpa only [descriptor, PreparedSegmentDescriptor.lottery_eq] using he

noncomputable def preparedDescriptorBitCost {k h : ℕ} (model : RationalCostModel) (G : RationalOverlapGluing k h) (B : ℚ) : ℕ :=
  descriptorBitCost model G B + (PreparedSegmentDescriptor.prepare (descriptorReference G B)).payloadBitCost

theorem preparedDescriptorBitCost_bound {k h : ℕ} (model : RationalCostModel) (G : RationalOverlapGluing k h) (B : ℚ)
    (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    preparedDescriptorBitCost model G B ≤ 2185 * (k * h) * model.rat (1 + 2 * expressionHeightBudget s 9) := by
  have hFormula := descriptorBitCost_bound model G B s hs hFirst hSecond hD hB
  have hReference : (descriptorReference G B).HeightAt (expressionHeightBudget s 9) := by
    rw [descriptorReference_eq]
    exact (G.descriptor_height B s hs hFirst hSecond hD hB).mono
      (expressionHeightBudget_mono s (by decide : 6 ≤ 9))
  have hPayload := (PreparedSegmentDescriptor.prepare (descriptorReference G B)).payloadBitCost_bound _ hReference
  have hCells : k * h + 2 * (k * h) * 4 = 9 * (k * h) := by ring
  rw [hCells] at hPayload
  have hCopies := hPayload.trans (Nat.mul_le_mul_left (9 * (k * h)) (model.word_le (1 + 2 * expressionHeightBudget s 9)))
  unfold preparedDescriptorBitCost
  nlinarith

end Blotto.RationalOverlapFormula
