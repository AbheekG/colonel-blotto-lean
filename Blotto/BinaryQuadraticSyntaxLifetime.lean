import Blotto.BinaryQuadraticExpressionLifetime
import Blotto.BinarySyntaxLifetime

/-! Source-syntax compilation joins the actual quadratic selected evaluator.
Only the unchanged portable compiler trace is reused from the earlier lane;
no Euclidean arithmetic allocation is assigned to quadratic execution. Source
environment heights and AST sizes derive the complete compiler/evaluator
reservation bound, including all selected branches and borrowed literals. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticSyntaxLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryExpressionCompiler BinarySyntaxUniformWork

def runWithTrace {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k) : SignedWord×Trace :=
  let compiled := BinarySyntaxLifetime.compileWithTrace source
  let evaluated := BinaryQuadraticExpressionLifetime.evaluate env compiled.1
  (evaluated.1,[.frames 2,.arrayAllocation 8] ++ under 2 compiled.2 ++ under 2 evaluated.2)

@[simp] theorem runWithTrace_erases {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k) :
    (runWithTrace env source).1=BinaryQuadraticData.expression env source.compile := by
  simp only [runWithTrace,BinarySyntaxLifetime.compileWithTrace_erases,BinaryQuadraticExpressionLifetime.evaluate_erases]

theorem runWithTrace_state {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k)
    (hC : ∀ j,CanonicalWord (env.read j)) : (runWithTrace env source).1=(source.compile.run env).1 := by
  rw [runWithTrace_erases]
  exact BinaryQuadraticData.expression_state source.compile env (fun j => (hC j).1)
    (source.compile.canonicalLiterals_valid source.compile_canonical)

def bound (nodes operations s D : ℕ) : ℕ :=
  6*nodes+operations*BinaryQuadraticExpressionLifetime.stepBound (8*expressionHeightBudget s D+7)+8
def frames (nodes s D : ℕ) : ℕ :=
  nodes+D+BinaryQuadraticExpressionLifetime.frameBound (8*expressionHeightBudget s D+7)+5

theorem runWithTrace_bounds {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k)
    (hC : ∀ j,CanonicalWord (env.read j)) (s D operations nodes : ℕ) (hs : 3≤s)
    (hH : EnvHeight env s) (hD : source.rational.depth≤D)
    (hOperations : source.rational.operationBound≤operations) (hNodes : source.nodes≤nodes) :
    listCells (runWithTrace env source).2+arraySlots (runWithTrace env source).2≤bound nodes operations s D ∧
    framePeak (runWithTrace env source).2≤frames nodes s D := by
  have hAll := source.rational.run_all_heights (BinaryRationalExpression.interpretedEnvironment env) s
    (interpreted_height env s hH) (literal_heights source s hs)
  have hBudget := RationalExpression.AllRunHeights_mono source.rational _ (expressionHeightBudget_mono s hD) hAll
  have hEval := BinaryQuadraticExpressionLifetime.evaluate_height_contract env source.compile hC source.compile_canonical
    (expressionHeightBudget s D) (by rw [source.compile_interpreted]; exact hBudget)
  rw [source.compile_interpreted] at hEval
  have hCount := Nat.mul_le_mul_right (BinaryQuadraticExpressionLifetime.stepBound (8*expressionHeightBudget s D+7)) hOperations
  have hCompile := source.compileAllocated_bound
  have hNodesTop := Nat.mul_le_mul_left 6 hNodes
  have hCompileFrames : framePeak (under 2 (BinarySyntaxLifetime.compileWithTrace source).2)≤source.nodes+4 := by
    simp [BinarySyntaxLifetime.compileWithTrace,under,shiftEvent,framePeak]
    omega
  simp only [BinarySyntaxLifetime.compileWithTrace] at hCompileFrames
  have hEvalFrames := framePeak_under 2 (BinaryQuadraticExpressionLifetime.evaluate env source.compile).2
  have hDepth := BinarySyntaxLifetime.depth_compile source
  unfold runWithTrace bound frames
  simp only [BinarySyntaxLifetime.compileWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,
    framePeak,listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

theorem run_all_prefix {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k)
    (hC : ∀ j,CanonicalWord (env.read j)) (s D operations nodes : ℕ) (hs : 3≤s)
    (hH : EnvHeight env s) (hD : source.rational.depth≤D)
    (hOperations : source.rational.operationBound≤operations) (hNodes : source.nodes≤nodes)
    (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells (runWithTrace env source).2 steps≤borrowedCells+bound nodes operations s D :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (runWithTrace_bounds env source hC s D operations nodes hs hH hD hOperations hNodes).1

end Blotto.BinaryQuadraticSyntaxLifetime
