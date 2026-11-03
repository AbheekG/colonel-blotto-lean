import Blotto.BinaryLifetimeUsage
import Blotto.BinaryOrderedThreeFactoryWork

/-! One actual five-word environment feeds the traced regime and four
geometry programs. Original fields derive compilation/evaluation reservations;
the geometry words themselves are consumed by the later regular factory. -/
namespace Blotto.BinaryThreeGeometryLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage BinaryThreeInputCompiler BinarySyntaxUniformWork
set_option maxHeartbeats 1500000

def environmentWithTrace (input : Input) : FixedArrayTable 5 SignedWord × Trace :=
  (input.environment,wrap 128 10 [])

theorem environmentWithTrace_usage (input : Input) : usage (environmentWithTrace input).2 ≤ 138 := by
  change usage (wrap 128 10 []) ≤ _
  have h := wrap_usage 128 10 []
  simpa only [List.map_nil,List.sum_nil,Nat.add_zero] using h

def geometryWithTrace (env : FixedArrayTable 5 SignedWord) : FixedArrayTable 4 SignedWord × Trace :=
  BinaryLifetimeArray.build 4 (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (parameters j))

theorem geometryWithTrace_erasure (env : FixedArrayTable 5 SignedWord) (hC : ∀ j,CanonicalWord (env.read j)) :
    (geometryWithTrace env).1 = FixedArrayTable.ofFn (fun j => ((parameters j).compile.run env).1) := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [geometryWithTrace,BinaryLifetimeArray.build_erases,FixedArrayTable.read_ofFn]
  exact BinaryQuadraticSyntaxLifetime.runWithTrace_state env (parameters j) hC

theorem parameter_nodes (j : Fin 4) : (parameters j).nodes ≤ 16 := by fin_cases j <;> decide
theorem regime_nodes : regime.nodes ≤ 16 := by decide

def geometryEnvelope (s : ℕ) : ℕ :=
  4 * BinaryQuadraticSyntaxLifetime.bound 16 16 s 2 + BinaryQuadraticSyntaxLifetime.frames 16 s 2 + 80

theorem geometryWithTrace_usage (env : FixedArrayTable 5 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hHeight : EnvHeight env s) : usage (geometryWithTrace env).2 ≤ geometryEnvelope s := by
  have hEach := fun j => BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env (parameters j) hC s 2 16 16 hs hHeight
    (BinaryOrderedThreeFactoryWork.parameter_sizes j).1 (BinaryOrderedThreeFactoryWork.parameter_sizes j).2 (parameter_nodes j)
  have h := array_usage 4 (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (parameters j))
    (BinaryQuadraticSyntaxLifetime.bound 16 16 s 2) (BinaryQuadraticSyntaxLifetime.frames 16 s 2)
    (fun j => (hEach j).1) (fun j => (hEach j).2)
  change usage (BinaryLifetimeArray.build 4 (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (parameters j))).2 ≤ _
  unfold geometryEnvelope
  omega

def regimeWithTrace (env : FixedArrayTable 5 SignedWord) : SignedWord × Trace :=
  BinaryQuadraticSyntaxLifetime.runWithTrace env regime

theorem regimeWithTrace_erasure (env : FixedArrayTable 5 SignedWord) (hC : ∀ j,CanonicalWord (env.read j)) :
    (regimeWithTrace env).1 = (regime.compile.run env).1 :=
  BinaryQuadraticSyntaxLifetime.runWithTrace_state env regime hC

def regimeEnvelope (s : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.bound 16 8 s 2 + BinaryQuadraticSyntaxLifetime.frames 16 s 2

theorem regimeWithTrace_usage (env : FixedArrayTable 5 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hHeight : EnvHeight env s) : usage (regimeWithTrace env).2 ≤ regimeEnvelope s := by
  have h := BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env regime hC s 2 8 16 hs hHeight
    BinaryOrderedThreeFactoryWork.regime_sizes.1 BinaryOrderedThreeFactoryWork.regime_sizes.2 regime_nodes
  unfold regimeWithTrace usage BinaryPRGHeapPrimitiveLifetime.cells regimeEnvelope
  omega

def comparisonEnvelope (W : ℕ) : ℕ := 2500 * (W + 1)^3 + 150 * (W + 1)^2 + 16

theorem comparison_usage (first second : SignedWord) (W : ℕ) (hFirst : width first ≤ W) (hSecond : width second ≤ W) :
    usage (BinaryQuadraticExpressionLifetime.compareWithTrace first second).2 ≤ comparisonEnvelope W := by
  have h := BinaryQuadraticExpressionLifetime.compareWithTrace_bounds first second W hFirst hSecond
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells comparisonEnvelope
  omega

end Blotto.BinaryThreeGeometryLifetime
