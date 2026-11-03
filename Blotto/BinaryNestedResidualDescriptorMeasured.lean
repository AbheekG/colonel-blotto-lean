import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryNestedResidualDescriptorLifetime
import Blotto.BinaryQuadraticSyntaxMeasured
import Blotto.BinaryLifetimeArrayMeasured

/-! Actual measured syntax evaluation produces all three residual weights and
both endpoint arrays through measured three-slot builders. Original canonical
five-word heights derive source work and enlarged retained-prefix bounds. -/
namespace Blotto.BinaryNestedResidualDescriptorMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryNestedResidualCompiler
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev Env := FixedArrayTable 5 SignedWord
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 3

set_option cleanup.letToHave false in
def weightsWithExtras (env : Env) : ((FixedArrayTable 3 SignedWord × Trace) × ℕ) × ℕ :=
  BinaryLifetimeArrayExtras.build 3 (fun slot => BinaryQuadraticSyntaxMeasured.runWithExtras env (BinaryNestedResidualCompiler.weights slot))

def weights (env : Env) : (FixedArrayTable 3 SignedWord × Trace) × ℕ :=
  (weightsWithExtras env).1

theorem weightsWithExtras_compat (env : Env) :
    (weightsWithExtras env).1 = weights env := rfl

theorem weights_record (env : Env) :
    weights env =
  BinaryLifetimeArrayMeasured.build 3 (fun slot => BinaryQuadraticSyntaxMeasured.run env (BinaryNestedResidualCompiler.weights slot)) := by
  simp only [weights,weightsWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat]

set_option cleanup.letToHave false in
def vertexRowWithExtras (env : Env) (vertex : Fin 3) : ((FixedArrayTable 3 SignedWord × Trace) × ℕ) × ℕ :=
  BinaryLifetimeArrayExtras.build 3 (fun j => BinaryQuadraticSyntaxMeasured.runWithExtras env (vertices vertex j))

def vertexRow (env : Env) (vertex : Fin 3) : (FixedArrayTable 3 SignedWord × Trace) × ℕ :=
  (vertexRowWithExtras env vertex).1

theorem vertexRowWithExtras_compat (env : Env) (vertex : Fin 3) :
    (vertexRowWithExtras env vertex).1 = vertexRow env vertex := rfl

theorem vertexRow_record (env : Env) (vertex : Fin 3) :
    vertexRow env vertex =
  BinaryLifetimeArrayMeasured.build 3 (fun j => BinaryQuadraticSyntaxMeasured.run env (vertices vertex j)) := by
  simp only [vertexRow,vertexRowWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat,weightsWithExtras_compat]

set_option cleanup.letToHave false in
def rowsWithExtras (env : Env) (edge : Fin 3 → Fin 3) : ((FixedArrayTable 3 (FixedArrayTable 3 SignedWord) × Trace) × ℕ) × ℕ :=
  BinaryLifetimeArrayExtras.build 3 (fun slot => vertexRowWithExtras env (edge slot))

def rows (env : Env) (edge : Fin 3 → Fin 3) : (FixedArrayTable 3 (FixedArrayTable 3 SignedWord) × Trace) × ℕ :=
  (rowsWithExtras env edge).1

theorem rowsWithExtras_compat (env : Env) (edge : Fin 3 → Fin 3) :
    (rowsWithExtras env edge).1 = rows env edge := rfl

theorem rows_record (env : Env) (edge : Fin 3 → Fin 3) :
    rows env edge =
  BinaryLifetimeArrayMeasured.build 3 (fun slot => vertexRow env (edge slot)) := by
  simp only [rows,rowsWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat,weightsWithExtras_compat,vertexRowWithExtras_compat]

set_option cleanup.letToHave false in
def descriptorWithExtras (env : Env) : ((Segment × Trace) × ℕ) × ℕ :=
  let weight := weightsWithExtras env
  let first := rowsWithExtras env (fun slot => (RationalNestedResidual.edges slot).1)
  let second := rowsWithExtras env (fun slot => (RationalNestedResidual.edges slot).2)
  (((⟨weight.1.1.1,first.1.1.1,second.1.1.1⟩,wrap 32 2 [weight.1.1.2,first.1.1.2,second.1.1.2]),weight.1.2+first.1.2+second.1.2+8),weight.2+first.2+second.2)

def descriptor (env : Env) : (Segment × Trace) × ℕ :=
  (descriptorWithExtras env).1

theorem descriptorWithExtras_compat (env : Env) :
    (descriptorWithExtras env).1 = descriptor env := rfl

theorem descriptor_record (env : Env) :
    descriptor env =
  let weight := weights env
  let first := rows env (fun slot => (RationalNestedResidual.edges slot).1)
  let second := rows env (fun slot => (RationalNestedResidual.edges slot).2)
  ((⟨weight.1.1,first.1.1,second.1.1⟩,wrap 32 2 [weight.1.2,first.1.2,second.1.2]),weight.2+first.2+second.2+8) := by
  simp only [descriptor,descriptorWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat,weightsWithExtras_compat,vertexRowWithExtras_compat,rowsWithExtras_compat]

theorem weights_data (env : Env) :
    (weights env).1.1 = (BinaryNestedResidualDescriptorLifetime.weightsWithTrace env).1 := by
  simp only [weights_record,BinaryNestedResidualDescriptorLifetime.weightsWithTrace,
    BinaryLifetimeArrayMeasured.build_data,BinaryQuadraticSyntaxMeasured.run_erases]

theorem vertexRow_data (env : Env) (vertex : Fin 3) :
    (vertexRow env vertex).1.1 = (BinaryNestedResidualDescriptorLifetime.vertexRowWithTrace env vertex).1 := by
  simp only [vertexRow_record,BinaryNestedResidualDescriptorLifetime.vertexRowWithTrace,
    BinaryLifetimeArrayMeasured.build_data,BinaryQuadraticSyntaxMeasured.run_erases]

theorem rows_data (env : Env) (edge : Fin 3 → Fin 3) :
    (rows env edge).1.1 = (BinaryNestedResidualDescriptorLifetime.rowsWithTrace env edge).1 := by
  simp only [rows_record,BinaryNestedResidualDescriptorLifetime.rowsWithTrace,
    BinaryLifetimeArrayMeasured.build_data,BinaryLifetimeArray.build_erases,vertexRow_data]

theorem descriptor_data (env : Env) :
    (descriptor env).1.1 = (BinaryNestedResidualDescriptorLifetime.descriptorWithTrace env).1 := by
  simp only [descriptor_record,BinaryNestedResidualDescriptorLifetime.descriptorWithTrace,weights_data,rows_data]

def expressionWork (s : ℕ) : ℕ := BinaryQuadraticSyntaxMeasured.workEnvelope 128 128 s 8
def expressionEnvelope (s : ℕ) : ℕ := BinaryNestedResidualDescriptorLifetime.expressionEnvelope s
def arrayPrice (P : ℕ) : ℕ := 3*P+1024
def arrayEnvelope (U : ℕ) : ℕ := 4*U+BinaryLifetimeArrayMeasured.storageReserve 3+16

def workEnvelope (s : ℕ) : ℕ := arrayPrice (expressionWork s)+2*arrayPrice (arrayPrice (expressionWork s))+8
def envelope (s : ℕ) : ℕ := arrayEnvelope (expressionEnvelope s)+2*arrayEnvelope (arrayEnvelope (expressionEnvelope s))+64

theorem weight_bounds (env : Env) (hC : ∀ j,CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) (slot : Fin 3) :
    (BinaryQuadraticSyntaxMeasured.run env (BinaryNestedResidualCompiler.weights slot)).2 ≤ expressionWork s ∧
      usage (BinaryQuadraticSyntaxMeasured.run env (BinaryNestedResidualCompiler.weights slot)).1.2 ≤ expressionEnvelope s := by
  refine ⟨BinaryQuadraticSyntaxMeasured.run_work env _ hC s 8 128 128 hs hH
    (BinaryNestedRemainingFactoryWork.residual_sizes slot).1 (BinaryNestedRemainingFactoryWork.residual_sizes slot).2
    (BinaryNestedResidualDescriptorLifetime.weight_nodes slot),?_⟩
  rw [BinaryQuadraticSyntaxMeasured.run_erases]
  exact BinaryNestedResidualDescriptorLifetime.weight_usage env hC s hs hH slot

theorem vertex_bounds (env : Env) (hC : ∀ j,CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) (vertex j : Fin 3) :
    (BinaryQuadraticSyntaxMeasured.run env (vertices vertex j)).2 ≤ expressionWork s ∧
      usage (BinaryQuadraticSyntaxMeasured.run env (vertices vertex j)).1.2 ≤ expressionEnvelope s := by
  refine ⟨BinaryQuadraticSyntaxMeasured.run_work env _ hC s 8 128 128 hs hH
    (BinaryNestedRemainingFactoryWork.residual_vertex_sizes vertex j).1 (BinaryNestedRemainingFactoryWork.residual_vertex_sizes vertex j).2
    (BinaryNestedResidualDescriptorLifetime.vertex_nodes vertex j),?_⟩
  rw [BinaryQuadraticSyntaxMeasured.run_erases]
  exact BinaryNestedResidualDescriptorLifetime.vertex_usage env hC s hs hH vertex j

theorem array_bounds {α : Type*} (produce : Fin 3 → (α × Trace) × ℕ) (P U : ℕ)
    (hEach : ∀ j,(produce j).2 ≤ P ∧ usage (produce j).1.2 ≤ U) :
    (BinaryLifetimeArrayMeasured.build 3 produce).2 ≤ arrayPrice P ∧
      usage (BinaryLifetimeArrayMeasured.build 3 produce).1.2 ≤ arrayEnvelope U := by
  have hw := BinaryLifetimeArrayMeasured.build_work_bound 3 produce P (fun j => (hEach j).1)
  have hu := BinaryLifetimeArrayMeasured.build_bounds 3 produce U U
    (by intro j; have h := (hEach j).2; unfold usage at h; omega)
    (by intro j; have h := (hEach j).2; unfold usage at h; omega)
  exact ⟨hw,hu.trans_eq (by unfold arrayEnvelope; omega)⟩

theorem weights_bounds (env : Env) (hC : ∀ j,CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) :
    (weights env).2 ≤ arrayPrice (expressionWork s) ∧ usage (weights env).1.2 ≤ arrayEnvelope (expressionEnvelope s) := by
  rw [weights_record]
  exact (
    array_bounds _ _ _ (weight_bounds env hC s hs hH)
  )

theorem vertexRow_bounds (env : Env) (hC : ∀ j,CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) (vertex : Fin 3) :
    (vertexRow env vertex).2 ≤ arrayPrice (expressionWork s) ∧ usage (vertexRow env vertex).1.2 ≤ arrayEnvelope (expressionEnvelope s) := by
  rw [vertexRow_record]
  exact (
    array_bounds _ _ _ (vertex_bounds env hC s hs hH vertex)
  )

theorem rows_bounds (env : Env) (edge : Fin 3 → Fin 3) (hC : ∀ j,CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) :
    (rows env edge).2 ≤ arrayPrice (arrayPrice (expressionWork s)) ∧
      usage (rows env edge).1.2 ≤ arrayEnvelope (arrayEnvelope (expressionEnvelope s)) := by
  rw [rows_record]
  exact (
    array_bounds _ _ _ (fun slot => vertexRow_bounds env hC s hs hH (edge slot))
  )

theorem descriptor_bounds (env : Env) (hC : ∀ j,CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) :
    (descriptor env).2 ≤ workEnvelope s ∧ usage (descriptor env).1.2 ≤ envelope s := by
  have hWeight := weights_bounds env hC s hs hH
  have hFirst := rows_bounds env (fun slot => (RationalNestedResidual.edges slot).1) hC s hs hH
  have hSecond := rows_bounds env (fun slot => (RationalNestedResidual.edges slot).2) hC s hs hH
  have hw := wrap_usage 32 2 [(weights env).1.2,(rows env (fun slot => (RationalNestedResidual.edges slot).1)).1.2,
    (rows env (fun slot => (RationalNestedResidual.edges slot).2)).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [descriptor_record]
  change (weights env).2+(rows env (fun slot => (RationalNestedResidual.edges slot).1)).2+
    (rows env (fun slot => (RationalNestedResidual.edges slot).2)).2+8 ≤ _ ∧ usage (wrap 32 2 [_,_,_]) ≤ _
  unfold workEnvelope envelope
  exact ⟨by omega,by omega⟩

theorem all_prefix (env : Env) (hC : ∀ j,CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptor env).1.2 steps ≤ borrowed+envelope s ∧ framePeak ((descriptor env).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptor_bounds env hC s hs hH).2 borrowed steps

end Blotto.BinaryNestedResidualDescriptorMeasured
