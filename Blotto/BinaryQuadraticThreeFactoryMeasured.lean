import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryQuadraticSyntaxMeasured
import Blotto.BinaryQuadraticThreeFactoryLifetime
import Blotto.BinaryLifetimeArrayMeasured

/-! The regular three-variable descriptor consumes each measured compiled
expression and each returned row once. All nested tables use the measured
source push-loop builder. Exact preceding descriptor data is retained; traces
have larger copied-reference/control reservations. Native model costs remain
separate. -/

namespace Blotto.BinaryQuadraticThreeFactoryMeasured
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinarySyntaxUniformWork BinaryThreeDescriptorCompiler BinaryFactoryHeight BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3500000

set_option cleanup.letToHave false in
def vertexRowWithExtras (env : FixedArrayTable 4 SignedWord) (i : Fin 6) : ((FixedArrayTable 3 SignedWord × Trace) × ℕ) × ℕ :=
  BinaryLifetimeArrayExtras.build 3 (fun j => BinaryQuadraticSyntaxMeasured.runWithExtras env (vertex i j))

def vertexRow (env : FixedArrayTable 4 SignedWord) (i : Fin 6) : (FixedArrayTable 3 SignedWord × Trace) × ℕ :=
  (vertexRowWithExtras env i).1

theorem vertexRowWithExtras_compat (env : FixedArrayTable 4 SignedWord) (i : Fin 6) :
    (vertexRowWithExtras env i).1 = vertexRow env i := rfl

theorem vertexRow_record (env : FixedArrayTable 4 SignedWord) (i : Fin 6) :
    vertexRow env i =
  BinaryLifetimeArrayMeasured.build 3 (fun j => BinaryQuadraticSyntaxMeasured.run env (vertex i j)) := by
  simp only [vertexRow,vertexRowWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat]

set_option cleanup.letToHave false in
def descriptorWithExtras (env : FixedArrayTable 4 SignedWord) : ((BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ) × ℕ :=
  let weight := BinaryLifetimeArrayExtras.build 9 (fun slot => BinaryQuadraticSyntaxMeasured.runWithExtras env (chosen slot))
  let first := BinaryLifetimeArrayExtras.build 9 (fun slot => vertexRowWithExtras env (RationalThreeGeometry.edges slot).1)
  let second := BinaryLifetimeArrayExtras.build 9 (fun slot => vertexRowWithExtras env (RationalThreeGeometry.edges slot).2)
  (((⟨weight.1.1.1,first.1.1.1,second.1.1.1⟩,wrap 32 2 [weight.1.1.2,first.1.1.2,second.1.1.2]),
    weight.1.2+first.1.2+second.1.2+8),weight.2+first.2+second.2)

def descriptor (env : FixedArrayTable 4 SignedWord) : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ :=
  (descriptorWithExtras env).1

theorem descriptorWithExtras_compat (env : FixedArrayTable 4 SignedWord) :
    (descriptorWithExtras env).1 = descriptor env := rfl

theorem descriptor_record (env : FixedArrayTable 4 SignedWord) :
    descriptor env =
  let weight := BinaryLifetimeArrayMeasured.build 9 (fun slot => BinaryQuadraticSyntaxMeasured.run env (chosen slot))
  let first := BinaryLifetimeArrayMeasured.build 9 (fun slot => vertexRow env (RationalThreeGeometry.edges slot).1)
  let second := BinaryLifetimeArrayMeasured.build 9 (fun slot => vertexRow env (RationalThreeGeometry.edges slot).2)
  ((⟨weight.1.1,first.1.1,second.1.1⟩,wrap 32 2 [weight.1.2,first.1.2,second.1.2]),
    weight.2+first.2+second.2+8) := by
  simp only [descriptor,descriptorWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat,vertexRowWithExtras_compat]

theorem vertexRow_data (env : FixedArrayTable 4 SignedWord) (i : Fin 6) :
    (vertexRow env i).1.1 = (BinaryQuadraticThreeFactoryLifetime.vertexRowWithTrace env i).1 := by
  simp only [vertexRow_record,BinaryLifetimeArrayMeasured.build_data,BinaryQuadraticSyntaxMeasured.run_erases,
    BinaryQuadraticThreeFactoryLifetime.vertexRowWithTrace]

theorem descriptor_data (env : FixedArrayTable 4 SignedWord) :
    (descriptor env).1.1 = (BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace env).1 := by
  simp only [descriptor_record,BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace,BinaryLifetimeArrayMeasured.build_data,
    BinaryQuadraticSyntaxMeasured.run_erases,BinaryLifetimeArray.build_erases,vertexRow_data]

def expressionWork (s : ℕ) : ℕ := BinaryQuadraticSyntaxMeasured.workEnvelope 256 256 s 16
def expressionCells (s : ℕ) : ℕ := BinaryQuadraticThreeFactoryLifetime.expressionBound s
def expressionFrames (s : ℕ) : ℕ := BinaryQuadraticThreeFactoryLifetime.expressionFrames s
def rowEnvelope (s : ℕ) : ℕ := 3*expressionCells s+BinaryLifetimeArrayMeasured.storageReserve 3+6+expressionFrames s+10
def rowsEnvelope (s : ℕ) : ℕ := 10*rowEnvelope s+BinaryLifetimeArrayMeasured.storageReserve 9+28
def workEnvelope (s : ℕ) : ℕ := 63*expressionWork s+40000
def envelope (s : ℕ) : ℕ := 128*(expressionCells s+expressionFrames s+1000)

theorem chosen_work (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) (slot : Fin 9) :
    (BinaryQuadraticSyntaxMeasured.run env (chosen slot)).2 ≤ expressionWork s :=
  BinaryQuadraticSyntaxMeasured.run_work env _ hC s 16 256 256 hs hH
    (BinaryThreeFactoryWork.chosen_sizes slot).1 (BinaryThreeFactoryWork.chosen_sizes slot).2
    (BinaryQuadraticThreeFactoryLifetime.chosen_nodes slot)

theorem vertex_work (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) (i : Fin 6) (j : Fin 3) :
    (BinaryQuadraticSyntaxMeasured.run env (vertex i j)).2 ≤ expressionWork s :=
  BinaryQuadraticSyntaxMeasured.run_work env _ hC s 16 256 256 hs hH
    (BinaryThreeFactoryWork.vertex_sizes i j).1 (BinaryThreeFactoryWork.vertex_sizes i j).2
    (BinaryQuadraticThreeFactoryLifetime.vertex_nodes i j)

theorem vertexRow_work (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) (i : Fin 6) :
    (vertexRow env i).2 ≤ 3*expressionWork s+1024 := by
  rw [vertexRow_record]
  exact BinaryLifetimeArrayMeasured.build_work_bound 3 _ _ (vertex_work env hC s hs hH i)

theorem descriptor_work (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) : (descriptor env).2 ≤ workEnvelope s := by
  have hw := BinaryLifetimeArrayMeasured.build_work_bound 9
    (fun slot => BinaryQuadraticSyntaxMeasured.run env (chosen slot)) _ (chosen_work env hC s hs hH)
  have hp := BinaryLifetimeArrayMeasured.build_work_bound 9
    (fun slot => vertexRow env (RationalThreeGeometry.edges slot).1) _ (fun _ => vertexRow_work env hC s hs hH _)
  have hq := BinaryLifetimeArrayMeasured.build_work_bound 9
    (fun slot => vertexRow env (RationalThreeGeometry.edges slot).2) _ (fun _ => vertexRow_work env hC s hs hH _)
  rw [descriptor_record]
  change _+_+_+8 ≤ _
  unfold workEnvelope
  nlinarith only [hw,hp,hq]

theorem vertexRow_usage (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) (i : Fin 6) : usage (vertexRow env i).1.2 ≤ rowEnvelope s := by
  rw [vertexRow_record]
  apply BinaryLifetimeArrayMeasured.build_bounds
  · intro j
    rw [BinaryQuadraticSyntaxMeasured.run_erases]
    exact (BinaryQuadraticThreeFactoryLifetime.vertex_bounds env hC s hs hH i j).1
  · intro j
    rw [BinaryQuadraticSyntaxMeasured.run_erases]
    exact (BinaryQuadraticThreeFactoryLifetime.vertex_bounds env hC s hs hH i j).2

theorem descriptor_usage (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) : usage (descriptor env).1.2 ≤ envelope s := by
  have hw := BinaryLifetimeArrayMeasured.build_bounds 9
    (fun slot => BinaryQuadraticSyntaxMeasured.run env (chosen slot)) (expressionCells s) (expressionFrames s)
    (fun slot => by rw [BinaryQuadraticSyntaxMeasured.run_erases]; exact (BinaryQuadraticThreeFactoryLifetime.chosen_bounds env hC s hs hH slot).1)
    (fun slot => by rw [BinaryQuadraticSyntaxMeasured.run_erases]; exact (BinaryQuadraticThreeFactoryLifetime.chosen_bounds env hC s hs hH slot).2)
  have hRow := vertexRow_usage env hC s hs hH
  have hCell : ∀ i,BinaryPRGHeapPrimitiveLifetime.cells (vertexRow env i).1.2 ≤ rowEnvelope s := by
    intro i
    have h := hRow i
    unfold usage at h
    omega
  have hFrame : ∀ i,framePeak (vertexRow env i).1.2 ≤ rowEnvelope s := by
    intro i
    have h := hRow i
    unfold usage at h
    omega
  have hp := BinaryLifetimeArrayMeasured.build_bounds 9 (fun slot => vertexRow env (RationalThreeGeometry.edges slot).1)
    (rowEnvelope s) (rowEnvelope s) (fun _ => hCell _) (fun _ => hFrame _)
  have hq := BinaryLifetimeArrayMeasured.build_bounds 9 (fun slot => vertexRow env (RationalThreeGeometry.edges slot).2)
    (rowEnvelope s) (rowEnvelope s) (fun _ => hCell _) (fun _ => hFrame _)
  have hr := wrap_usage 32 2
    [(BinaryLifetimeArrayMeasured.build 9 (fun slot => BinaryQuadraticSyntaxMeasured.run env (chosen slot))).1.2,
      (BinaryLifetimeArrayMeasured.build 9 (fun slot => vertexRow env (RationalThreeGeometry.edges slot).1)).1.2,
      (BinaryLifetimeArrayMeasured.build 9 (fun slot => vertexRow env (RationalThreeGeometry.edges slot).2)).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hr
  rw [descriptor_record]
  change usage (wrap 32 2 [_,_,_]) ≤ _
  unfold envelope rowEnvelope BinaryLifetimeArrayMeasured.storageReserve at *
  omega

theorem all_prefix (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptor env).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((descriptor env).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptor_usage env hC s hs hH) borrowed steps

end Blotto.BinaryQuadraticThreeFactoryMeasured
