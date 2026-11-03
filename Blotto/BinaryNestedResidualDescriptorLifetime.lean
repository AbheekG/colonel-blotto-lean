import Blotto.BinaryNestedSecondProfileLifetime

/-! The three-slot residual descriptor is produced by traced quadratic syntax
evaluation of all three weights and both three-by-three endpoint arrays. -/
namespace Blotto.BinaryNestedResidualDescriptorLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage BinaryNestedResidualCompiler
set_option maxHeartbeats 2000000

abbrev Env := FixedArrayTable 5 SignedWord
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 3

def weightsWithTrace (env : Env) : FixedArrayTable 3 SignedWord × Trace :=
  BinaryLifetimeArray.build 3 (fun slot =>
    BinaryQuadraticSyntaxLifetime.runWithTrace env (weights slot))

def vertexRowWithTrace (env : Env) (vertex : Fin 3) : FixedArrayTable 3 SignedWord × Trace :=
  BinaryLifetimeArray.build 3 (fun j =>
    BinaryQuadraticSyntaxLifetime.runWithTrace env (vertices vertex j))

def rowsWithTrace (env : Env) (edge : Fin 3 → Fin 3) :
    FixedArrayTable 3 (FixedArrayTable 3 SignedWord) × Trace :=
  BinaryLifetimeArray.build 3 (fun slot => vertexRowWithTrace env (edge slot))

def descriptorWithTrace (env : Env) : Segment × Trace :=
  let weight := weightsWithTrace env
  let first := rowsWithTrace env (fun slot => (RationalNestedResidual.edges slot).1)
  let second := rowsWithTrace env (fun slot => (RationalNestedResidual.edges slot).2)
  (⟨weight.1,first.1,second.1⟩,wrap 32 2 [weight.2,first.2,second.2])

theorem descriptorWithTrace_erasure (env : Env) (hC : ∀ j,CanonicalWord (env.read j)) :
    (descriptorWithTrace env).1 = BinaryNestedResidualCompiler.descriptor env := by
  simp only [descriptorWithTrace,weightsWithTrace,rowsWithTrace,vertexRowWithTrace,
    BinaryLifetimeArray.build_erases,BinaryQuadraticSyntaxLifetime.runWithTrace_state env _ hC,
    BinaryNestedResidualCompiler.descriptor]

theorem weight_nodes (slot : Fin 3) : (weights slot).nodes ≤ 128 := by
  fin_cases slot <;> decide

theorem vertex_nodes (vertex j : Fin 3) : (vertices vertex j).nodes ≤ 128 := by
  fin_cases vertex <;> fin_cases j <;> decide

def expressionEnvelope (s : ℕ) : ℕ :=
  BinaryQuadraticSyntaxLifetime.bound 128 128 s 8 +
    BinaryQuadraticSyntaxLifetime.frames 128 s 8

theorem weight_usage (env : Env) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySyntaxUniformWork.EnvHeight env s) (slot : Fin 3) :
    usage (BinaryQuadraticSyntaxLifetime.runWithTrace env (weights slot)).2 ≤ expressionEnvelope s := by
  have h := BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env (weights slot) hC
    s 8 128 128 hs hH (BinaryNestedRemainingFactoryWork.residual_sizes slot).1
      (BinaryNestedRemainingFactoryWork.residual_sizes slot).2 (weight_nodes slot)
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells expressionEnvelope
  omega

theorem vertex_usage (env : Env) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySyntaxUniformWork.EnvHeight env s) (vertex j : Fin 3) :
    usage (BinaryQuadraticSyntaxLifetime.runWithTrace env (vertices vertex j)).2 ≤ expressionEnvelope s := by
  have h := BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env (vertices vertex j) hC
    s 8 128 128 hs hH (BinaryNestedRemainingFactoryWork.residual_vertex_sizes vertex j).1
      (BinaryNestedRemainingFactoryWork.residual_vertex_sizes vertex j).2 (vertex_nodes vertex j)
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells expressionEnvelope
  omega

def arrayEnvelope (B : ℕ) : ℕ := 4 * B + 64

theorem weightsWithTrace_usage (env : Env) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySyntaxUniformWork.EnvHeight env s) :
    usage (weightsWithTrace env).2 ≤ arrayEnvelope (expressionEnvelope s) := by
  have hEach := fun slot => weight_usage env hC s hs hH slot
  have ha := array_usage 3 (fun slot => BinaryQuadraticSyntaxLifetime.runWithTrace env (weights slot))
    (expressionEnvelope s) (expressionEnvelope s)
    (by intro slot; have h := hEach slot; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at h; omega)
    (by intro slot; have h := hEach slot; unfold usage at h; omega)
  change usage (BinaryLifetimeArray.build 3
    (fun slot => BinaryQuadraticSyntaxLifetime.runWithTrace env (weights slot))).2 ≤ _
  unfold arrayEnvelope
  omega

theorem vertexRowWithTrace_usage (env : Env) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySyntaxUniformWork.EnvHeight env s) (vertex : Fin 3) :
    usage (vertexRowWithTrace env vertex).2 ≤ arrayEnvelope (expressionEnvelope s) := by
  have hEach := fun j => vertex_usage env hC s hs hH vertex j
  have ha := array_usage 3 (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (vertices vertex j))
    (expressionEnvelope s) (expressionEnvelope s)
    (by intro j; have h := hEach j; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at h; omega)
    (by intro j; have h := hEach j; unfold usage at h; omega)
  change usage (BinaryLifetimeArray.build 3
    (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (vertices vertex j))).2 ≤ _
  unfold arrayEnvelope
  omega

theorem rowsWithTrace_usage (env : Env) (edge : Fin 3 → Fin 3)
    (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySyntaxUniformWork.EnvHeight env s) :
    usage (rowsWithTrace env edge).2 ≤ arrayEnvelope (arrayEnvelope (expressionEnvelope s)) := by
  have hEach := fun slot => vertexRowWithTrace_usage env hC s hs hH (edge slot)
  have ha := array_usage 3 (fun slot => vertexRowWithTrace env (edge slot))
    (arrayEnvelope (expressionEnvelope s)) (arrayEnvelope (expressionEnvelope s))
    (by intro slot; have h := hEach slot; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at h; omega)
    (by intro slot; have h := hEach slot; unfold usage at h; omega)
  change usage (BinaryLifetimeArray.build 3 (fun slot => vertexRowWithTrace env (edge slot))).2 ≤ _
  unfold arrayEnvelope at ha ⊢
  omega

def envelope (s : ℕ) : ℕ := arrayEnvelope (expressionEnvelope s) +
  2 * arrayEnvelope (arrayEnvelope (expressionEnvelope s)) + 128

theorem descriptorWithTrace_usage (env : Env) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySyntaxUniformWork.EnvHeight env s) :
    usage (descriptorWithTrace env).2 ≤ envelope s := by
  have hwg := weightsWithTrace_usage env hC s hs hH
  have hp := rowsWithTrace_usage env (fun slot => (RationalNestedResidual.edges slot).1) hC s hs hH
  have hq := rowsWithTrace_usage env (fun slot => (RationalNestedResidual.edges slot).2) hC s hs hH
  have hw := wrap_usage 32 2
    [(weightsWithTrace env).2,
      (rowsWithTrace env (fun slot => (RationalNestedResidual.edges slot).1)).2,
      (rowsWithTrace env (fun slot => (RationalNestedResidual.edges slot).2)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2
    [(weightsWithTrace env).2,
      (rowsWithTrace env (fun slot => (RationalNestedResidual.edges slot).1)).2,
      (rowsWithTrace env (fun slot => (RationalNestedResidual.edges slot).2)).2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (env : Env) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySyntaxUniformWork.EnvHeight env s) (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptorWithTrace env).2 steps ≤ borrowed + envelope s ∧
    framePeak ((descriptorWithTrace env).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptorWithTrace_usage env hC s hs hH) borrowed steps

end Blotto.BinaryNestedResidualDescriptorLifetime
