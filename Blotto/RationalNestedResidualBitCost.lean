import Blotto.RationalNestedResidualCode
import Blotto.RationalExpressionBitCost
import Blotto.PreparedSegmentDescriptorHeight

/-! Every residual descriptor weight and endpoint is priced, including zero
weights. Materialization is one table construction; caller factory repetition,
environment derivation, addresses, allocation and backend remain separate. -/

namespace Blotto.RationalNestedResidualCode
open scoped BigOperators

theorem weight_bitCost (model : RationalCostModel) (r : RationalNestedResidual) (slot : Fin 3)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment r).read j) s) :
    (weights slot).bitCost model (environment r) ≤ 128 * model.rat (1 + 2 * expressionHeightBudget s 8) :=
  ((weights slot).bitCost_bound model _ _ (weight_intermediates r slot s hs hEnv)).trans
    (Nat.mul_le_mul_right _ (weight_operationBound slot))

theorem vertex_intermediates (r : RationalNestedResidual) (slot j : Fin 3) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment r).read j) s) :
    (vertices slot j).AllRunHeights (environment r) (expressionHeightBudget s 8) := by
  have h := (vertices slot j).run_all_heights _ s hEnv
    ((vertices slot j).LiteralHeights_mono hs (vertex_literals slot j))
  exact RationalExpression.AllRunHeights_mono _ _
    (expressionHeightBudget_mono s ((vertex_depth slot j).trans (by decide : 3 ≤ 8))) h

theorem vertex_bitCost (model : RationalCostModel) (r : RationalNestedResidual) (slot j : Fin 3)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment r).read j) s) :
    (vertices slot j).bitCost model (environment r) ≤ 16 * model.rat (1 + 2 * expressionHeightBudget s 8) :=
  ((vertices slot j).bitCost_bound model _ _ (vertex_intermediates r slot j s hs hEnv)).trans
    (Nat.mul_le_mul_right _ (vertex_operationBound slot j))

def descriptorBitCost (model : RationalCostModel) (r : RationalNestedResidual) : ℕ :=
  (∑ slot : Fin 3, (weights slot).bitCost model (environment r)) +
    (∑ slot : Fin 3, ∑ j : Fin 3, (vertices (RationalNestedResidual.edges slot).1 j).bitCost model (environment r)) +
    (∑ slot : Fin 3, ∑ j : Fin 3, (vertices (RationalNestedResidual.edges slot).2 j).bitCost model (environment r))

theorem descriptorBitCost_bound (model : RationalCostModel) (r : RationalNestedResidual)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment r).read j) s) :
    descriptorBitCost model r ≤ 672 * model.rat (1 + 2 * expressionHeightBudget s 8) := by
  let price := model.rat (1 + 2 * expressionHeightBudget s 8)
  have hw : (∑ slot : Fin 3, (weights slot).bitCost model (environment r)) ≤ 3 * (128 * price) := by
    calc
      _ ≤ ∑ _slot : Fin 3, 128 * price := Finset.sum_le_sum (fun slot _ => weight_bitCost model r slot s hs hEnv)
      _ = _ := by simp
  have hp : (∑ slot : Fin 3, ∑ j : Fin 3, (vertices (RationalNestedResidual.edges slot).1 j).bitCost model (environment r)) ≤ 3 * (3 * (16 * price)) := by
    calc
      _ ≤ ∑ _slot : Fin 3, ∑ _j : Fin 3, 16 * price := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => vertex_bitCost model r _ j s hs hEnv))
      _ = _ := by simp
  have hq : (∑ slot : Fin 3, ∑ j : Fin 3, (vertices (RationalNestedResidual.edges slot).2 j).bitCost model (environment r)) ≤ 3 * (3 * (16 * price)) := by
    calc
      _ ≤ ∑ _slot : Fin 3, ∑ _j : Fin 3, 16 * price := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => vertex_bitCost model r _ j s hs hEnv))
      _ = _ := by simp
  change descriptorBitCost model r ≤ 672 * price
  unfold descriptorBitCost
  omega

def preparedDescriptorBitCost (model : RationalCostModel) (r : RationalNestedResidual) : ℕ :=
  descriptorBitCost model r + (PreparedSegmentDescriptor.prepare r.segmentLottery).payloadBitCost

theorem preparedDescriptorBitCost_bound (model : RationalCostModel) (r : RationalNestedResidual)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment r).read j) s) :
    preparedDescriptorBitCost model r ≤ 693 * model.rat (1 + 2 * expressionHeightBudget s 8) := by
  have hf := descriptorBitCost_bound model r s hs hEnv
  have hp := (PreparedSegmentDescriptor.prepare r.segmentLottery).payloadBitCost_bound _ (descriptor_height r s hs hEnv)
  have hc := hp.trans (Nat.mul_le_mul_left 21 (model.word_le (1 + 2 * expressionHeightBudget s 8)))
  unfold preparedDescriptorBitCost
  omega

def descriptorArithmeticWork (r : RationalNestedResidual) : ℕ :=
  (∑ slot : Fin 3, ((weights slot).run (environment r)).2) +
    (∑ slot : Fin 3, ∑ j : Fin 3, ((vertices (RationalNestedResidual.edges slot).1 j).run (environment r)).2) +
    (∑ slot : Fin 3, ∑ j : Fin 3, ((vertices (RationalNestedResidual.edges slot).2 j).run (environment r)).2)

theorem descriptorArithmeticWork_bound (r : RationalNestedResidual) : descriptorArithmeticWork r ≤ 672 := by
  have hw : (∑ slot : Fin 3, ((weights slot).run (environment r)).2) ≤ 3 * 128 := by
    calc
      _ ≤ ∑ _slot : Fin 3, 128 := Finset.sum_le_sum (fun slot _ => weight_operations r slot)
      _ = _ := by simp
  have hp : (∑ slot : Fin 3, ∑ j : Fin 3, ((vertices (RationalNestedResidual.edges slot).1 j).run (environment r)).2) ≤ 3 * (3 * 16) := by
    calc
      _ ≤ ∑ _slot : Fin 3, ∑ _j : Fin 3, 16 := Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ =>
        ((vertices _ j).run_operations_le _).trans (vertex_operationBound _ j)))
      _ = _ := by simp
  have hq : (∑ slot : Fin 3, ∑ j : Fin 3, ((vertices (RationalNestedResidual.edges slot).2 j).run (environment r)).2) ≤ 3 * (3 * 16) := by
    calc
      _ ≤ ∑ _slot : Fin 3, ∑ _j : Fin 3, 16 := Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ =>
        ((vertices _ j).run_operations_le _).trans (vertex_operationBound _ j)))
      _ = _ := by simp
  unfold descriptorArithmeticWork
  omega

end Blotto.RationalNestedResidualCode
