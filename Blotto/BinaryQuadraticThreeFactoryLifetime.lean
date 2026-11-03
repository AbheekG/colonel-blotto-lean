import Blotto.BinaryQuadraticSyntaxLifetime
import Blotto.BinaryLifetimeArray
import Blotto.BinaryThreeFactoryWork

/-! The actual regular three-variable factory, with source compilation,
selected quadratic expression evaluation and all nested array reservations. The output
is produced by the traced evaluator itself. All 9 weights and both 9-by-3
endpoint tables equal the original descriptor; actual environment heights
and checked source AST sizes derive storage and source-activation bounds.
Every reached arithmetic allocation uses the actual Stein-GCD backend. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticThreeFactoryLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinarySyntaxUniformWork BinaryThreeDescriptorCompiler BinaryFactoryHeight

def vertexRowWithTrace (env : FixedArrayTable 4 SignedWord) (i : Fin 6) :
    FixedArrayTable 3 SignedWord × Trace :=
  BinaryLifetimeArray.build 3 (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (vertex i j))

def descriptorWithTrace (env : FixedArrayTable 4 SignedWord) : BinaryStoredOverlapEnvironment.Segment 3 9 × Trace :=
  let weight := BinaryLifetimeArray.build 9 (fun slot => BinaryQuadraticSyntaxLifetime.runWithTrace env (chosen slot))
  let first := BinaryLifetimeArray.build 9 (fun slot => vertexRowWithTrace env (RationalThreeGeometry.edges slot).1)
  let second := BinaryLifetimeArray.build 9 (fun slot => vertexRowWithTrace env (RationalThreeGeometry.edges slot).2)
  (⟨weight.1,first.1,second.1⟩,[.frames 3,.arrayAllocation 8] ++
    under 2 weight.2 ++ under 2 first.2 ++ under 2 second.2)

@[simp] theorem vertexRowWithTrace_erases (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j)) (i : Fin 6) :
    (vertexRowWithTrace env i).1=FixedArrayTable.ofFn (fun j => ((vertex i j).compile.run env).1) := by
  simp only [vertexRowWithTrace,BinaryLifetimeArray.build_erases,BinaryQuadraticSyntaxLifetime.runWithTrace_state env _ hC]

@[simp] theorem descriptorWithTrace_erases (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j)) :
    (descriptorWithTrace env).1=descriptor env := by
  simp only [descriptorWithTrace,BinaryLifetimeArray.build_erases,BinaryQuadraticSyntaxLifetime.runWithTrace_state env _ hC,
    vertexRowWithTrace_erases env hC,descriptor]

theorem chosen_nodes (slot : Fin 9) : (chosen slot).nodes ≤ 256 := by fin_cases slot <;> decide
theorem vertex_nodes (i : Fin 6) (j : Fin 3) : (vertex i j).nodes ≤ 256 := by fin_cases i <;> fin_cases j <;> decide

def expressionBound (s : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.bound 256 256 s 16
def expressionFrames (s : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.frames 256 s 16
def bound (s : ℕ) : ℕ := 63*expressionBound s+1352
def frames (s : ℕ) : ℕ := expressionFrames s+26

theorem chosen_bounds (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) (slot : Fin 9) :
    listCells (BinaryQuadraticSyntaxLifetime.runWithTrace env (chosen slot)).2+
      arraySlots (BinaryQuadraticSyntaxLifetime.runWithTrace env (chosen slot)).2 ≤ expressionBound s ∧
    framePeak (BinaryQuadraticSyntaxLifetime.runWithTrace env (chosen slot)).2 ≤ expressionFrames s := by
  exact BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env _ hC s 16 256 256 hs hH
    (BinaryThreeFactoryWork.chosen_sizes slot).1 (BinaryThreeFactoryWork.chosen_sizes slot).2 (chosen_nodes slot)

theorem vertex_bounds (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) (i : Fin 6) (j : Fin 3) :
    listCells (BinaryQuadraticSyntaxLifetime.runWithTrace env (vertex i j)).2+
      arraySlots (BinaryQuadraticSyntaxLifetime.runWithTrace env (vertex i j)).2 ≤ expressionBound s ∧
    framePeak (BinaryQuadraticSyntaxLifetime.runWithTrace env (vertex i j)).2 ≤ expressionFrames s := by
  exact BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env _ hC s 16 256 256 hs hH
    (BinaryThreeFactoryWork.vertex_sizes i j).1 (BinaryThreeFactoryWork.vertex_sizes i j).2 (vertex_nodes i j)

theorem vertexRowWithTrace_bounds (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) (i : Fin 6) :
    listCells (vertexRowWithTrace env i).2+arraySlots (vertexRowWithTrace env i).2 ≤ 3*expressionBound s+40 ∧
    framePeak (vertexRowWithTrace env i).2 ≤ expressionFrames s+9 := by
  have h := BinaryLifetimeArray.build_bounds 3 (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (vertex i j))
    (expressionBound s) (expressionFrames s)
    (fun j => (vertex_bounds env hC s hs hH i j).1) (fun j => (vertex_bounds env hC s hs hH i j).2)
  change _≤3*expressionBound s+40 ∧ _≤3+expressionFrames s+6 at h
  exact ⟨h.1,by unfold vertexRowWithTrace; omega⟩

theorem descriptorWithTrace_bounds (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) :
    listCells (descriptorWithTrace env).2+arraySlots (descriptorWithTrace env).2 ≤ bound s ∧
    framePeak (descriptorWithTrace env).2 ≤ frames s := by
  have hw := BinaryLifetimeArray.build_bounds 9 (fun slot => BinaryQuadraticSyntaxLifetime.runWithTrace env (chosen slot))
    (expressionBound s) (expressionFrames s) (fun slot => (chosen_bounds env hC s hs hH slot).1)
    (fun slot => (chosen_bounds env hC s hs hH slot).2)
  have hp := BinaryLifetimeArray.build_bounds 9 (fun slot => vertexRowWithTrace env (RationalThreeGeometry.edges slot).1)
    (3*expressionBound s+40) (expressionFrames s+9) (fun slot => (vertexRowWithTrace_bounds env hC s hs hH _).1)
    (fun slot => (vertexRowWithTrace_bounds env hC s hs hH _).2)
  have hq := BinaryLifetimeArray.build_bounds 9 (fun slot => vertexRowWithTrace env (RationalThreeGeometry.edges slot).2)
    (3*expressionBound s+40) (expressionFrames s+9) (fun slot => (vertexRowWithTrace_bounds env hC s hs hH _).1)
    (fun slot => (vertexRowWithTrace_bounds env hC s hs hH _).2)
  have hwf := framePeak_under 2 (BinaryLifetimeArray.build 9 (fun slot => BinaryQuadraticSyntaxLifetime.runWithTrace env (chosen slot))).2
  have hpf := framePeak_under 2 (BinaryLifetimeArray.build 9 (fun slot => vertexRowWithTrace env (RationalThreeGeometry.edges slot).1)).2
  have hqf := framePeak_under 2 (BinaryLifetimeArray.build 9 (fun slot => vertexRowWithTrace env (RationalThreeGeometry.edges slot).2)).2
  unfold descriptorWithTrace bound frames
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

theorem descriptor_all_prefix (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells (descriptorWithTrace env).2 steps ≤ borrowedCells+bound s := by
  have hb := (descriptorWithTrace_bounds env hC s hs hH).1
  have hl := listCells_take_le (descriptorWithTrace env).2 steps
  have ha := arraySlots_take_le (descriptorWithTrace env).2 steps
  unfold retainedHeap
  omega

end Blotto.BinaryQuadraticThreeFactoryLifetime
