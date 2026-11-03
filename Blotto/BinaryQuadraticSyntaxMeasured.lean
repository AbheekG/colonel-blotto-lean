import Blotto.BinaryQuadraticExpressionMeasured
import Blotto.BinaryQuadraticSyntaxLifetime

/-! Structural compilation consumes each source child once, then the actual
compiled expression feeds measured selected evaluation. The finite literal
alphabet has bounded Boolean payload. Charges reserve source constructor/control
work; native environment/reference/observer/allocator prices remain separate. -/

namespace Blotto.BinaryQuadraticSyntaxMeasured
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryExpressionCompiler BinarySyntaxUniformWork BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

def compile {k : ℕ} : Syntax k → BinaryRationalExpression k × ℕ
  | .input j => (.input j,12)
  | .literal c => (.literal c.word,12)
  | .add a b => let x := compile a; let y := compile b; (.add x.1 y.1,x.2+y.2+12)
  | .sub a b => let x := compile a; let y := compile b; (.sub x.1 y.1,x.2+y.2+12)
  | .mul a b => let x := compile a; let y := compile b; (.mul x.1 y.1,x.2+y.2+12)
  | .div a b => let x := compile a; let y := compile b; (.div x.1 y.1,x.2+y.2+12)
  | .minimum a b => let x := compile a; let y := compile b; (.minimum x.1 y.1,x.2+y.2+12)
  | .maximum a b => let x := compile a; let y := compile b; (.maximum x.1 y.1,x.2+y.2+12)
  | .ifLe a b yes no =>
      let x := compile a
      let y := compile b
      let t := compile yes
      let f := compile no
      (.ifLe x.1 y.1 t.1 f.1,x.2+y.2+t.2+f.2+12)

theorem compile_data {k : ℕ} (source : Syntax k) : (compile source).1 = source.compile := by
  induction source <;> simp only [compile,Syntax.compile, *]

theorem compile_work {k : ℕ} (source : Syntax k) : (compile source).2 = 12*source.nodes := by
  induction source <;> simp only [compile,Syntax.nodes, *] <;> omega

def compileWithTrace {k : ℕ} (source : Syntax k) : (BinaryRationalExpression k × Trace) × ℕ :=
  let compiled := compile source
  ((compiled.1,[.frames (source.nodes+2),.listAllocation source.compileAllocated]),compiled.2)

theorem compile_erases {k : ℕ} (source : Syntax k) :
    (compileWithTrace source).1 = BinarySyntaxLifetime.compileWithTrace source := by
  simp only [compileWithTrace,BinarySyntaxLifetime.compileWithTrace,compile_data]

set_option cleanup.letToHave false in
def runWithExtras {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k) : ((SignedWord × Trace) × ℕ) × ℕ :=
  let compiled := compileWithTrace source
  let produced := BinaryQuadraticExpressionMeasured.evaluateWithExtras env compiled.1.1
  let evaluated := produced.1
  (((evaluated.1.1,[.frames 2,.arrayAllocation 8]++under 2 compiled.1.2++under 2 evaluated.1.2),
    compiled.2+evaluated.2+8),produced.2)

def run {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k) : (SignedWord × Trace) × ℕ :=
  (runWithExtras env source).1

theorem runWithExtras_compat {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k) :
    (runWithExtras env source).1 = run env source := rfl

theorem run_record {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k) :
    run env source =
  let compiled := compileWithTrace source
  let evaluated := BinaryQuadraticExpressionMeasured.evaluate env compiled.1.1
  ((evaluated.1.1,[.frames 2,.arrayAllocation 8]++under 2 compiled.1.2++under 2 evaluated.1.2),
    compiled.2+evaluated.2+8)
 := by
  rfl

theorem run_erases {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k) :
    (run env source).1 = BinaryQuadraticSyntaxLifetime.runWithTrace env source := by
  simp only [run_record,BinaryQuadraticSyntaxLifetime.runWithTrace,compile_erases,
    BinaryQuadraticExpressionMeasured.evaluate_erases]

def workEnvelope (nodes operations s D : ℕ) : ℕ :=
  12*nodes+operations*BinaryQuadraticExpression.uniformPrice (expressionHeightBudget s D)+8

theorem run_work {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k)
    (hC : ∀ j,CanonicalWord (env.read j)) (s D operations nodes : ℕ) (hs : 3 ≤ s)
    (hH : EnvHeight env s) (hD : source.rational.depth ≤ D)
    (hOperations : source.rational.operationBound ≤ operations) (hNodes : source.nodes ≤ nodes) :
    (run env source).2 ≤ workEnvelope nodes operations s D := by
  have hAll := source.rational.run_all_heights (BinaryRationalExpression.interpretedEnvironment env) s
    (interpreted_height env s hH) (literal_heights source s hs)
  have hBudget := RationalExpression.AllRunHeights_mono source.rational _ (expressionHeightBudget_mono s hD) hAll
  have hEval := BinaryQuadraticExpressionMeasured.evaluate_work_bound env source.compile hC source.compile_canonical
    (expressionHeightBudget s D) (by rw [source.compile_interpreted]; exact hBudget)
  rw [source.compile_interpreted] at hEval
  have hCount := Nat.mul_le_mul_right (BinaryQuadraticExpression.uniformPrice (expressionHeightBudget s D)) hOperations
  have hNode := Nat.mul_le_mul_left 12 hNodes
  simp only [run_record,compileWithTrace,compile_data,compile_work,workEnvelope]
  omega

theorem run_bounds {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k)
    (hC : ∀ j,CanonicalWord (env.read j)) (s D operations nodes : ℕ) (hs : 3 ≤ s)
    (hH : EnvHeight env s) (hD : source.rational.depth ≤ D)
    (hOperations : source.rational.operationBound ≤ operations) (hNodes : source.nodes ≤ nodes) :
    BinaryPRGHeapPrimitiveLifetime.cells (run env source).1.2 ≤ BinaryQuadraticSyntaxLifetime.bound nodes operations s D ∧
      framePeak (run env source).1.2 ≤ BinaryQuadraticSyntaxLifetime.frames nodes s D := by
  rw [run_erases]
  exact BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env source hC s D operations nodes hs hH hD hOperations hNodes

theorem run_all_prefix {k : ℕ} (env : FixedArrayTable k SignedWord) (source : Syntax k)
    (hC : ∀ j,CanonicalWord (env.read j)) (s D operations nodes : ℕ) (hs : 3 ≤ s)
    (hH : EnvHeight env s) (hD : source.rational.depth ≤ D)
    (hOperations : source.rational.operationBound ≤ operations) (hNodes : source.nodes ≤ nodes)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (run env source).1.2 steps ≤ borrowed+
      (BinaryQuadraticSyntaxLifetime.bound nodes operations s D+BinaryQuadraticSyntaxLifetime.frames nodes s D) ∧
    framePeak ((run env source).1.2.take steps) ≤
      BinaryQuadraticSyntaxLifetime.bound nodes operations s D+BinaryQuadraticSyntaxLifetime.frames nodes s D := by
  have h := run_bounds env source hC s D operations nodes hs hH hD hOperations hNodes
  apply BinaryPRGHeapTraceUsage.all_prefix
  unfold usage
  exact Nat.add_le_add h.1 h.2

end Blotto.BinaryQuadraticSyntaxMeasured
