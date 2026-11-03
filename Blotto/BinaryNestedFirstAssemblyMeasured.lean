import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryNestedReferenceMeasured
import Blotto.BinaryReflectedSystemMeasured
import Blotto.BinaryNestedFirstAssemblyLifetime

/-! Actual measured reference construction forms the zero-probability corner.
Eighteen measured additions and row/array packing translate a regular table's
third coordinate. Exact old data and source-width bounds are retained. -/
namespace Blotto.BinaryNestedFirstAssemblyMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryLifetimeUsage
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 700000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 9

def corner (input : Input) (x : SignedWord) : (Segment × Trace) × ℕ :=
  BinaryThreeReferenceMeasured.assemble ![BinaryRationalOpcode.zero,input.d,x] ![input.a,BinaryRationalOpcode.zero,x]

theorem corner_data (input : Input) (x : SignedWord) :
    (corner input x).1.1 = (BinaryNestedFirstAssemblyLifetime.cornerWithTrace input x).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,corner,BinaryThreeReferenceMeasured.assemble,BinaryThreeReferenceMeasured.references_data,
    BinaryThreeReferenceMeasured.rows_data,BinaryNestedFirstAssemblyLifetime.cornerWithTrace,
    BinaryThreeReferenceLifetime.weightsWithTrace,BinaryThreeReferenceLifetime.rowsWithTrace,
    BinaryThreeReferenceLifetime.rowWithTrace,BinaryLifetimeArray.build_erases]

theorem corner_bounds (input : Input) (x : SignedWord) :
    (corner input x).2 ≤ 50000 ∧ usage (corner input x).1.2 ≤ 50000 :=
  ⟨BinaryThreeReferenceMeasured.assemble_work _ _ (by decide),BinaryThreeReferenceMeasured.assemble_usage _ _ (by decide)⟩

def rowFrom (row : FixedArrayTable 3 SignedWord) (added : (SignedWord × Trace) × ℕ) :
    (FixedArrayTable 3 SignedWord × Trace) × ℕ :=
  let built := BinaryThreeReferenceMeasured.references 3 ![row.read 0,row.read 1,added.1.1]
  ((built.1.1,wrap 24 2 [added.1.2,built.1.2]),added.2+built.2+8)

set_option cleanup.letToHave false in
def rowShiftWithExtras (row : FixedArrayTable 3 SignedWord) (x : SignedWord) : ((FixedArrayTable 3 SignedWord × Trace) × ℕ) × ℕ :=
  let added := BinaryNormalizedCoordinate.opcode .add (row.read 2) x
  (rowFrom row added.1,added.2)

def rowShift (row : FixedArrayTable 3 SignedWord) (x : SignedWord) : (FixedArrayTable 3 SignedWord × Trace) × ℕ :=
  (rowShiftWithExtras row x).1

theorem rowShiftWithExtras_compat (row : FixedArrayTable 3 SignedWord) (x : SignedWord) :
    (rowShiftWithExtras row x).1 = rowShift row x := rfl

theorem rowShift_record (row : FixedArrayTable 3 SignedWord) (x : SignedWord) :
    rowShift row x =
  rowFrom row (BinaryPlannedQuadratic.apply .add (row.read 2) x) := by
  simp only [rowShift,rowShiftWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record]

theorem rowShift_data (row : FixedArrayTable 3 SignedWord) (x : SignedWord) :
    (rowShift row x).1.1 = (BinaryNestedFirstAssemblyLifetime.rowShiftWithTrace row x).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,rowShift_record,rowFrom,BinaryNestedFirstAssemblyLifetime.rowShiftWithTrace,
    BinaryThreeReferenceMeasured.references_data,BinaryThreeReferenceLifetime.rowWithTrace,
    BinaryLifetimeArray.build_erases,BinaryQuadraticMeasured.apply_erases]

def rowPrice (W : ℕ) : ℕ := BinaryReflectedSystemMeasured.opcodePrice W+1100
def rowEnvelope (W : ℕ) : ℕ := opcodeEnvelope W+700

theorem rowFrom_bounds (row : FixedArrayTable 3 SignedWord) (added : (SignedWord × Trace) × ℕ) (P U : ℕ)
    (h : added.2 ≤ P ∧ usage added.1.2 ≤ U) :
    (rowFrom row added).2 ≤ P+1100 ∧ usage (rowFrom row added).1.2 ≤ U+700 := by
  let built := BinaryThreeReferenceMeasured.references 3 ![row.read 0,row.read 1,added.1.1]
  have hbW : built.2 ≤ 1036 := BinaryThreeReferenceMeasured.references_work 3 _
  have hbU : usage built.1.2 ≤ 617 := BinaryThreeReferenceMeasured.references_usage 3 _
  have hw := wrap_usage 24 2 [added.1.2,built.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change added.2+built.2+8 ≤ _ ∧ usage (wrap 24 2 [added.1.2,built.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem rowShift_bounds (row : FixedArrayTable 3 SignedWord) (x : SignedWord) (W : ℕ)
    (hRow : width (row.read 2) ≤ W) (hX : width x ≤ W) :
    (rowShift row x).2 ≤ rowPrice W ∧ usage (rowShift row x).1.2 ≤ rowEnvelope W := by
  simp only [rowShift_record, BinaryPlannedQuadratic.apply_previous]
  exact rowFrom_bounds _ _ _ _ (BinaryReflectedSystemMeasured.opcode_bounds .add _ _ W hRow hX)

set_option cleanup.letToHave false in
def rowsShiftWithExtras (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) : ((FixedArrayTable 9 (FixedArrayTable 3 SignedWord) × Trace) × ℕ) × ℕ :=
  BinaryLifetimeArrayExtras.build 9 (fun slot => rowShiftWithExtras (rows.read slot) x)

def rowsShift (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) :
    (FixedArrayTable 9 (FixedArrayTable 3 SignedWord) × Trace) × ℕ :=
  (rowsShiftWithExtras rows x).1

theorem rowsShiftWithExtras_compat (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) :
    (rowsShiftWithExtras rows x).1 = rowsShift rows x := rfl

theorem rowsShift_record (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) :
    rowsShift rows x =
  BinaryLifetimeArrayMeasured.build 9 (fun slot => rowShift (rows.read slot) x) := by
  simp only [rowsShift,rowsShiftWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record,rowShiftWithExtras_compat]

theorem rowsShift_data (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) :
    (rowsShift rows x).1.1 = (BinaryNestedFirstAssemblyLifetime.rowsShiftWithTrace rows x).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,rowsShift_record,BinaryNestedFirstAssemblyLifetime.rowsShiftWithTrace,
    BinaryLifetimeArrayMeasured.build_data,BinaryLifetimeArray.build_erases,rowShift_data]

def rowsPrice (W : ℕ) : ℕ := 9*rowPrice W+6400
def rowsEnvelope (W : ℕ) : ℕ := 10*rowEnvelope W+BinaryLifetimeArrayMeasured.storageReserve 9+28

theorem rowsShift_bounds (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) (W : ℕ)
    (hRows : ∀ slot,width ((rows.read slot).read 2) ≤ W) (hX : width x ≤ W) :
    (rowsShift rows x).2 ≤ rowsPrice W ∧ usage (rowsShift rows x).1.2 ≤ rowsEnvelope W := by
  have hEach := fun slot => rowShift_bounds (rows.read slot) x W (hRows slot) hX
  have hW := BinaryLifetimeArrayMeasured.build_work_bound 9 (fun slot => rowShift (rows.read slot) x) _ (fun slot => (hEach slot).1)
  have hU := BinaryLifetimeArrayMeasured.build_bounds 9 (fun slot => rowShift (rows.read slot) x) (rowEnvelope W) (rowEnvelope W)
    (by intro slot; have h := (hEach slot).2; unfold usage at h; omega)
    (by intro slot; have h := (hEach slot).2; unfold usage at h; omega)
  refine ⟨hW,?_⟩
  exact hU.trans_eq (by unfold rowsEnvelope; omega)

set_option cleanup.letToHave false in
def shiftWithExtras (table : Segment) (x : SignedWord) : ((Segment × Trace) × ℕ) × ℕ :=
  let first := rowsShiftWithExtras table.P x
  let second := rowsShiftWithExtras table.Q x
  (((⟨table.weight,first.1.1.1,second.1.1.1⟩,wrap 32 2 [first.1.1.2,second.1.1.2]),first.1.2+second.1.2+8),first.2+second.2)

def shift (table : Segment) (x : SignedWord) : (Segment × Trace) × ℕ :=
  (shiftWithExtras table x).1

theorem shiftWithExtras_compat (table : Segment) (x : SignedWord) :
    (shiftWithExtras table x).1 = shift table x := rfl

theorem shift_record (table : Segment) (x : SignedWord) :
    shift table x =
  let first := rowsShift table.P x
  let second := rowsShift table.Q x
  ((⟨table.weight,first.1.1,second.1.1⟩,wrap 32 2 [first.1.2,second.1.2]),first.2+second.2+8) := by
  simp only [shift,shiftWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record,rowShiftWithExtras_compat,rowsShiftWithExtras_compat]

theorem shift_data (table : Segment) (x : SignedWord) :
    (shift table x).1.1 = (BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace table x).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,shift_record,BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace,rowsShift_data]

def shiftPrice (W : ℕ) : ℕ := 2*rowsPrice W+8
def shiftEnvelope (W : ℕ) : ℕ := 2*rowsEnvelope W+64

theorem shift_bounds (table : Segment) (x : SignedWord) (W : ℕ)
    (hP : ∀ slot,width ((table.P.read slot).read 2) ≤ W)
    (hQ : ∀ slot,width ((table.Q.read slot).read 2) ≤ W) (hX : width x ≤ W) :
    (shift table x).2 ≤ shiftPrice W ∧ usage (shift table x).1.2 ≤ shiftEnvelope W := by
  have hp := rowsShift_bounds table.P x W hP hX
  have hq := rowsShift_bounds table.Q x W hQ hX
  have hw := wrap_usage 32 2 [(rowsShift table.P x).1.2,(rowsShift table.Q x).1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [shift_record]
  change (rowsShift table.P x).2+(rowsShift table.Q x).2+8 ≤ _ ∧ usage (wrap 32 2 [_,_]) ≤ _
  unfold shiftPrice shiftEnvelope
  exact ⟨by omega,by omega⟩

end Blotto.BinaryNestedFirstAssemblyMeasured
