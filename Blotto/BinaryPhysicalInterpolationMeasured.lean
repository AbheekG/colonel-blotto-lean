import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryPhysicalOutputMeasured
import Blotto.BinaryPhysicalInterpolationWork

/-! Returned measured endpoint heaps and Boolean indices feed actual measured
reads and all four affine opcodes. Full preceding row/trace and exact preceding
source work are preserved. Native projection/packing and reference/observer/
allocator prices remain caller/model obligations. -/

namespace Blotto.BinaryPhysicalInterpolationMeasured
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryWordObjectArray
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 4000000

def coordinate (first second scalar : SignedWord) : (SignedWord × Trace) × ℕ :=
  (BinaryNormalizedCoordinate.coordinate first second scalar).1

theorem coordinate_erases (first second scalar : SignedWord) :
    (coordinate first second scalar).1 = BinaryPhysicalInterpolation.coordinateWithTrace first second scalar := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryNormalizedCoordinate.coordinate_record,coordinate,BinaryPhysicalInterpolation.coordinateWithTrace,BinaryQuadraticMeasured.apply_erases]

theorem coordinate_data (first second scalar : SignedWord) :
    (coordinate first second scalar).1.1 = (BinaryPhysicalInterpolation.coordinateWithWork first second scalar).1 := by
  rw [coordinate_erases,← BinaryPhysicalInterpolation.coordinate_work_state]

theorem coordinate_work (first second scalar : SignedWord) :
    (coordinate first second scalar).2 = (BinaryPhysicalInterpolation.coordinateWithWork first second scalar).2 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryNormalizedCoordinate.coordinate_record,coordinate,BinaryPhysicalInterpolation.coordinateWithWork,BinaryQuadraticMeasured.apply_data,
    BinaryQuadraticMeasured.apply_work]

def loopWithExtras {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) :
    List (List Bool) → ((Option (List SignedWord) × Trace) × ℕ) × ℕ
  | [] => (((some [],wrap 16 1 []),4),0)
  | index::indices =>
      let p := BinaryWordObjectArrayAccessMeasured.get first index
      match p.1.1 with
      | none => (((none,wrap 24 2 [p.1.2]),p.2+8),0)
      | some wordP =>
          let q := BinaryWordObjectArrayAccessMeasured.get second index
          match q.1.1 with
          | none => (((none,wrap 32 2 [p.1.2,q.1.2]),p.2+q.2+8),0)
          | some wordQ =>
              let coordinate := BinaryNormalizedCoordinate.coordinate wordP wordQ scalar
              let later := loopWithExtras first second scalar indices
              (((later.1.1.1.map (fun rest => coordinate.1.1.1::rest),
                wrapList 1 64 2 [p.1.2,q.1.2,coordinate.1.1.2,later.1.1.2]),
                p.2+q.2+coordinate.1.2+later.1.2+16),coordinate.2+later.2)

def loop {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) :
    List (List Bool) → (Option (List SignedWord) × Trace) × ℕ :=
  fun indices => (loopWithExtras first second scalar indices).1

theorem loopWithExtras_compat {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord)
    (indices : List (List Bool)) : (loopWithExtras first second scalar indices).1 =
      loop first second scalar indices := rfl

theorem loop_record {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord)
    (indices : List (List Bool)) : loop first second scalar indices =
  match indices with
  | [] => ((some [],wrap 16 1 []),4)
  | index::indices =>
      let p := BinaryWordObjectArrayAccessMeasured.get first index
      match p.1.1 with
      | none => ((none,wrap 24 2 [p.1.2]),p.2+8)
      | some wordP =>
          let q := BinaryWordObjectArrayAccessMeasured.get second index
          match q.1.1 with
          | none => ((none,wrap 32 2 [p.1.2,q.1.2]),p.2+q.2+8)
          | some wordQ =>
              let coordinate := coordinate wordP wordQ scalar
              let later := loop first second scalar indices
              ((later.1.1.map (fun rest => coordinate.1.1::rest),
                wrapList 1 64 2 [p.1.2,q.1.2,coordinate.1.2,later.1.2]),p.2+q.2+coordinate.2+later.2+16) := by
  cases indices with
  | nil => rfl
  | cons index indices =>
      simp only [loop,loopWithExtras]
      cases hp : (BinaryWordObjectArrayAccessMeasured.get first index).1.1 with
      | none => simp only [hp]
      | some wordP =>
          simp only [hp]
          cases hq : (BinaryWordObjectArrayAccessMeasured.get second index).1.1 with
          | none => simp only [hq]
          | some wordQ => simp only [hq,coordinate]

theorem loop_nil {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) :
    loop first second scalar [] = ((some [],wrap 16 1 []),4) := rfl

theorem loop_cons {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord)
    (index : List Bool) (indices : List (List Bool)) : loop first second scalar (index::indices) =
      let p := BinaryWordObjectArrayAccessMeasured.get first index
      match p.1.1 with
      | none => ((none,wrap 24 2 [p.1.2]),p.2+8)
      | some wordP =>
          let q := BinaryWordObjectArrayAccessMeasured.get second index
          match q.1.1 with
          | none => ((none,wrap 32 2 [p.1.2,q.1.2]),p.2+q.2+8)
          | some wordQ =>
              let coordinate := coordinate wordP wordQ scalar
              let later := loop first second scalar indices
              ((later.1.1.map (fun rest => coordinate.1.1::rest),
                wrapList 1 64 2 [p.1.2,q.1.2,coordinate.1.2,later.1.2]),p.2+q.2+coordinate.2+later.2+16) := by
  simpa only using loop_record first second scalar (index::indices)

theorem loop_erases {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) (indices : List (List Bool)) :
    (loop first second scalar indices).1 = BinaryPhysicalInterpolationRow.loopWithTrace first second scalar indices := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,loop_nil,loop_cons,BinaryPhysicalInterpolationRow.loopWithTrace,BinaryWordObjectArrayAccessMeasured.get_erases]
      cases hp : (BinaryWordObjectArrayAccess.getWithTrace first index).1 with
      | none => simp only
      | some p =>
          cases hq : (BinaryWordObjectArrayAccess.getWithTrace second index).1 with
          | none => simp only
          | some q => simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,coordinate_erases,ih]

theorem loop_data {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) (indices : List (List Bool)) :
    (loop first second scalar indices).1.1 = (BinaryPhysicalInterpolationWork.loopWithWork first second scalar indices).1 := by
  rw [loop_erases,← BinaryPhysicalInterpolationWork.loop_state]

theorem loop_work {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord) (indices : List (List Bool)) :
    (loop first second scalar indices).2 = (BinaryPhysicalInterpolationWork.loopWithWork first second scalar indices).2 := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,loop_nil,loop_cons,BinaryPhysicalInterpolationWork.loopWithWork,BinaryWordObjectArrayAccessMeasured.get_data,
        BinaryWordObjectArrayAccessMeasured.get_work]
      cases hp : (getWithWork first index).1 with
      | none => simp only
      | some p =>
          cases hq : (getWithWork second index).1 with
          | none => simp only
          | some q => simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,coordinate_data,coordinate_work,ih]

set_option cleanup.letToHave false in
def runWithExtras (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) :
    ((List SignedWord × Trace) × ℕ) × ℕ :=
  let first := BinaryWordObjectArrayMeasured.prepare p
  let second := BinaryWordObjectArrayMeasured.prepare q
  let indices := BooleanArrayIndexMeasured.enumerate p
  let produced := loopWithExtras first.1.1 second.1.1 scalar indices.1.1
  let row := produced.1
  have hSome : row.1.1.isSome := by
    change (loop first.1.1 second.1.1 scalar indices.1.1).1.1.isSome
    rw [loop_erases,BinaryWordObjectArrayMeasured.prepare_state,BinaryWordObjectArrayMeasured.prepare_state,
      BooleanArrayIndexMeasured.enumerate_erases,BinaryPhysicalInterpolationRow.loop_enumerate _ _ p q
        (prepare_realizes p) (prepare_realizes q) hLength scalar]
    rfl
  (((row.1.1.get hSome,wrap 64 2 [first.1.2,second.1.2,indices.1.2,row.1.2]),
    first.2+second.2+indices.2+row.2+16),produced.2)

def run (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) : (List SignedWord × Trace) × ℕ :=
  (runWithExtras scalar p q hLength).1

theorem runWithExtras_compat (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) :
    (runWithExtras scalar p q hLength).1 = run scalar p q hLength := rfl

set_option cleanup.letToHave false in
theorem run_record (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) :
    run scalar p q hLength =
  let first := BinaryWordObjectArrayMeasured.prepare p
  let second := BinaryWordObjectArrayMeasured.prepare q
  let indices := BooleanArrayIndexMeasured.enumerate p
  let row := loop first.1.1 second.1.1 scalar indices.1.1
  have hSome : row.1.1.isSome := by
    rw [loop_erases,BinaryWordObjectArrayMeasured.prepare_state,BinaryWordObjectArrayMeasured.prepare_state,
      BooleanArrayIndexMeasured.enumerate_erases,BinaryPhysicalInterpolationRow.loop_enumerate _ _ p q
        (prepare_realizes p) (prepare_realizes q) hLength scalar]
    rfl
  ((row.1.1.get hSome,wrap 64 2 [first.1.2,second.1.2,indices.1.2,row.1.2]),
    first.2+second.2+indices.2+row.2+16) := by rfl

theorem run_erases (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) :
    (run scalar p q hLength).1 = BinaryPhysicalInterpolationRun.runWithTrace scalar p q hLength := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,run_record,BinaryPhysicalInterpolationRun.runWithTrace,BinaryWordObjectArrayMeasured.prepare_erases,
    BooleanArrayIndexMeasured.enumerate_erases,loop_erases]

theorem run_data (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) :
    (run scalar p q hLength).1.1 = (BinaryPhysicalInterpolationWork.runWithWork scalar p q hLength).1 := by
  rw [run_erases,← BinaryPhysicalInterpolationWork.run_state]

theorem run_work (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) :
    (run scalar p q hLength).2 = (BinaryPhysicalInterpolationWork.runWithWork scalar p q hLength).2 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,run_record,BinaryPhysicalInterpolationWork.runWithWork,BinaryWordObjectArrayMeasured.prepare_work,
    BooleanArrayIndexMeasured.enumerate_work,loop_work,BinaryPhysicalOutputMeasured.prepared_data,
    BinaryPhysicalOutputMeasured.indices_data]

theorem run_bound (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length)
    (hT : BinaryRationalOpcode.Valid scalar) (W : ℕ) (hW : 1 ≤ W) (ht : width scalar ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    (run scalar p q hLength).2 ≤ BinaryPhysicalInterpolationRun.bound p.length W := by
  rw [run_work]
  exact BinaryPhysicalInterpolationWork.run_work scalar p q hLength hT W hW ht hp hq

theorem all_prefix (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length)
    (hT : BinaryRationalOpcode.Valid scalar) (W : ℕ) (hW : 1 ≤ W) (ht : width scalar ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (run scalar p q hLength).1.2 steps ≤ borrowed+BinaryPhysicalInterpolationRun.bound p.length W ∧
      framePeak ((run scalar p q hLength).1.2.take steps) ≤ BinaryPhysicalInterpolationRun.bound p.length W := by
  rw [run_erases]
  exact BinaryPhysicalInterpolationRun.all_prefix scalar p q hLength hT W hW ht hp hq borrowed steps

end Blotto.BinaryPhysicalInterpolationMeasured
