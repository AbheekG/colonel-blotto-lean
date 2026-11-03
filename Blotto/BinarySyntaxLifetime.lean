import Blotto.BinaryExpressionLifetime
import Blotto.BinarySyntaxUniformWork

/-! Source-syntax compilation and selected evaluation reservations, with
heights derived from the actual input environment and finite syntax sizes.
The caller supplies no intermediate-word or execution-trace premise. The
arithmetic allocation backend is the retained Boolean Euclidean implementation.
Traces are annotations: explicit erasure preserves the original stored bytes.
List/array reservations and activations remain retained until return. -/
set_option autoImplicit false
namespace Blotto.BinarySyntaxLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryExpressionCompiler BinarySyntaxUniformWork

def compileWithTrace {k : ℕ} (source : Syntax k) : BinaryRationalExpression k × Trace :=
  (source.compile,[.frames (source.nodes+2),.listAllocation source.compileAllocated])

@[simp] theorem compileWithTrace_erases {k : ℕ} (source : Syntax k) :
    (compileWithTrace source).1=source.compile := rfl

def runWithTrace {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k) : SignedWord × Trace :=
  let compiled := compileWithTrace source
  let evaluated := BinaryExpressionLifetime.evaluate env compiled.1
  (evaluated.1,[.frames 2,.arrayAllocation 8] ++ under 2 compiled.2 ++ under 2 evaluated.2)

@[simp] theorem runWithTrace_erases {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k) :
    (runWithTrace env source).1=(source.compile.run env).1 := by
  simp only [runWithTrace,compileWithTrace_erases,BinaryExpressionLifetime.evaluate_erases]

theorem depth_compile {k : ℕ} (source : Syntax k) : source.compile.depth=source.rational.depth := by
  induction source <;> simp [Syntax.compile,Syntax.rational,BinaryRationalExpression.depth,RationalExpression.depth, *]

def bound (nodes operations s D : ℕ) : ℕ :=
  6*nodes+operations*BinaryExpressionLifetime.stepBound (8*expressionHeightBudget s D+7)+8

theorem runWithTrace_bounds {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k)
    (hC : ∀ j,CanonicalWord (env.read j)) (s D operations nodes : ℕ) (hs : 3 ≤ s)
    (hH : EnvHeight env s) (hD : source.rational.depth ≤ D)
    (hOperations : source.rational.operationBound ≤ operations) (hNodes : source.nodes ≤ nodes) :
    listCells (runWithTrace env source).2+arraySlots (runWithTrace env source).2 ≤ bound nodes operations s D ∧
    framePeak (runWithTrace env source).2 ≤ nodes+D+5 := by
  have hAll := source.rational.run_all_heights (BinaryRationalExpression.interpretedEnvironment env) s
    (interpreted_height env s hH) (literal_heights source s hs)
  have hBudget := RationalExpression.AllRunHeights_mono source.rational _ (expressionHeightBudget_mono s hD) hAll
  have hEval := BinaryExpressionLifetime.evaluate_height_contract env source.compile hC source.compile_canonical
    (expressionHeightBudget s D) (by rw [source.compile_interpreted]; exact hBudget)
  rw [source.compile_interpreted] at hEval
  have hCount := Nat.mul_le_mul_right (BinaryExpressionLifetime.stepBound (8*expressionHeightBudget s D+7)) hOperations
  have hCompile := source.compileAllocated_bound
  have hNodesTop := Nat.mul_le_mul_left 6 hNodes
  have hCompileFrames : framePeak (under 2 (compileWithTrace source).2) ≤ source.nodes+4 := by
    simp [compileWithTrace,under,shiftEvent,framePeak]
    omega
  simp only [compileWithTrace] at hCompileFrames
  have hEvalFrames := framePeak_under 2 (BinaryExpressionLifetime.evaluate env source.compile).2
  have hDepth := depth_compile source
  unfold runWithTrace bound
  simp only [compileWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

theorem runWithTrace_all_prefix {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k)
    (hC : ∀ j,CanonicalWord (env.read j)) (s D operations nodes : ℕ) (hs : 3 ≤ s)
    (hH : EnvHeight env s) (hD : source.rational.depth ≤ D)
    (hOperations : source.rational.operationBound ≤ operations) (hNodes : source.nodes ≤ nodes)
    (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells (runWithTrace env source).2 steps ≤ borrowedCells+bound nodes operations s D := by
  have hb := (runWithTrace_bounds env source hC s D operations nodes hs hH hD hOperations hNodes).1
  have hl := listCells_take_le (runWithTrace env source).2 steps
  have ha := arraySlots_take_le (runWithTrace env source).2 steps
  unfold retainedHeap
  omega

end Blotto.BinarySyntaxLifetime
