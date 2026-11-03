import Blotto.BinaryFactoryHeight
import Blotto.BinaryThreeDescriptorCompiler

/-! The actual regular three-variable table has source-independent finite-AST
height and primitive work bounds. They apply to conditional geometry computed
at runtime, without a supplied geometry-source or intermediate-height oracle. -/

namespace Blotto.BinaryThreeFactoryWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler
open BinaryThreeDescriptorCompiler BinarySyntaxUniformWork BinaryFactoryHeight
open scoped BigOperators

theorem chosen_sizes (slot : Fin 9) : (chosen slot).rational.depth ≤ 16 ∧
    (chosen slot).rational.operationBound ≤ 256 := by fin_cases slot <;> decide

theorem vertex_sizes (slot : Fin 6) (j : Fin 3) : (vertex slot j).rational.depth ≤ 16 ∧
    (vertex slot j).rational.operationBound ≤ 256 := by fin_cases slot <;> fin_cases j <;> decide

theorem descriptor_height (env : FixedArrayTable 4 SignedWord) (hC : ∀ j, CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) :
    SegmentHeight (descriptor env) (expressionHeightBudget s 16) := by
  refine ⟨?_,?_⟩
  · intro slot
    rw [descriptor,FixedArrayTable.read_ofFn]
    exact run_height_bound _ _ hC s 16 hs hH (chosen_sizes slot).1
  · intro slot j
    constructor
    · rw [descriptor,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
      exact run_height_bound _ _ hC s 16 hs hH (vertex_sizes _ j).1
    · rw [descriptor,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
      exact run_height_bound _ _ hC s 16 hs hH (vertex_sizes _ j).1

def bound (s : ℕ) : ℕ := 16128 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) + 25000

theorem descriptorWork_bound (env : FixedArrayTable 4 SignedWord) (hC : ∀ j, CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) :
    BinaryThreeDescriptorCompiler.descriptorWork env ≤ bound s := by
  have hc := fun slot => BinarySyntaxUniformWork.bitWork_bound (chosen slot) env hC s 16 256 hs hH
    (chosen_sizes slot).1 (chosen_sizes slot).2
  have hv := fun slot j => BinarySyntaxUniformWork.bitWork_bound (vertex slot j) env hC s 16 256 hs hH
    (vertex_sizes slot j).1 (vertex_sizes slot j).2
  have hcSum : (∑ slot : Fin 9, (chosen slot).compile.bitWork env) ≤
      2304 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) :=
    (Finset.sum_le_sum (fun slot _ => hc slot)).trans_eq (by simp; ring)
  have hpSum : (∑ slot : Fin 9, ∑ j : Fin 3, (vertex (RationalThreeGeometry.edges slot).1 j).compile.bitWork env) ≤
      6912 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) :=
    (Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hv _ j))).trans_eq (by simp; ring)
  have hqSum : (∑ slot : Fin 9, ∑ j : Fin 3, (vertex (RationalThreeGeometry.edges slot).2 j).compile.bitWork env) ≤
      6912 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) :=
    (Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hv _ j))).trans_eq (by simp; ring)
  unfold BinaryThreeDescriptorCompiler.descriptorWork bound
  omega

end Blotto.BinaryThreeFactoryWork
