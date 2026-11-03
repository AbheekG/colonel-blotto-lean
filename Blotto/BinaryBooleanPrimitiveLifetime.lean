import Blotto.BinarySeedPreparationSpace
import Blotto.BinaryRationalOpcodeAllocation

/-! Concrete unchanged Boolean primitives used by the quadratic backend.
Scans, signed borrow differences, restoring long division and reverse/drop/
reverse trimming have source reservation traces and exact data erasure.
The arithmetic allocation producers are the actual shared raw primitives;
no Euclidean GCD or Euclidean normalizer is called by these wrappers. All
reservations stay retained, with borrowed input payload counted separately.
These are Boolean/list/reference slots and source activations, not host bytes.
-/
set_option autoImplicit false
namespace Blotto.BinaryBooleanPrimitiveLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization

def scanWithTrace : List Bool → Bool×Trace
  | [] => (false,[.frames 1,.arrayAllocation 4])
  | bit::rest =>
      if bit then (true,[.frames 1,.arrayAllocation 4]) else
        let later := scanWithTrace rest
        (later.1,[.frames 1,.arrayAllocation 4] ++ under 1 later.2)

@[simp] theorem scanWithTrace_erases (bits : List Bool) :
    (scanWithTrace bits).1=BinaryEuclideanGCD.nonzero bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [scanWithTrace,BinaryEuclideanGCD.nonzero,ih]

theorem scanWithTrace_bounds (bits : List Bool) :
    listCells (scanWithTrace bits).2+arraySlots (scanWithTrace bits).2 ≤ 4*(bits.length+1) ∧
    framePeak (scanWithTrace bits).2 ≤ bits.length+1 := by
  induction bits with
  | nil => simp [scanWithTrace,listCells,arraySlots,framePeak]
  | cons bit rest ih =>
      cases bit
      · have hf := framePeak_under 1 (scanWithTrace rest).2
        simp only [scanWithTrace,Bool.false_eq_true,ite_false,listCells_append,arraySlots_append,
          framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under,List.length_cons]
        exact ⟨by omega,by omega⟩
      · simp [scanWithTrace,listCells,arraySlots,framePeak]

def differenceWithTrace (first second : List Bool) : BinarySignedMagnitude.Word×Trace :=
  let result := BinarySignedAllocation.differenceWithAllocation first second
  (result.1,[.frames (2*max first.length second.length+8),.arrayAllocation 8,
    .listAllocation (BinarySignedAllocation.differenceStorage first second)])

@[simp] theorem differenceWithTrace_erases (first second : List Bool) :
    (differenceWithTrace first second).1=BinarySignedMagnitude.difference first second :=
  BinarySignedAllocation.differenceWithAllocation_state first second

theorem differenceWithTrace_bounds (first second : List Bool) (W : ℕ)
    (hA : first.length≤W) (hB : second.length≤W) :
    listCells (differenceWithTrace first second).2+arraySlots (differenceWithTrace first second).2 ≤ 40*(W+1)^2+8 ∧
    framePeak (differenceWithTrace first second).2 ≤ 2*W+8 := by
  have hs := BinarySignedAllocation.differenceStorage_bound first second W hA hB
  have hw := max_le hA hB
  simp only [differenceWithTrace,listCells,arraySlots,framePeak]
  exact ⟨by omega,by omega⟩

def divideWithTrace (dividend divisor : List Bool) : (List Bool×List Bool)×Trace :=
  let result := BinaryDivisionAllocation.divideWithAllocation dividend divisor
  (result.1,[.frames (dividend.length+2*divisor.length+16),.arrayAllocation 8,
    .listAllocation (BinaryDivisionAllocation.divideStorage dividend divisor)])

@[simp] theorem divideWithTrace_erases (dividend divisor : List Bool) :
    (divideWithTrace dividend divisor).1=BinaryLongDivision.divide dividend divisor :=
  BinaryDivisionAllocation.divideWithAllocation_state dividend divisor

theorem divideWithTrace_bounds (dividend divisor : List Bool) (W : ℕ)
    (hA : dividend.length≤W) (hB : divisor.length≤W) :
    listCells (divideWithTrace dividend divisor).2+arraySlots (divideWithTrace dividend divisor).2 ≤ 500*(W+2)^3+8 ∧
    framePeak (divideWithTrace dividend divisor).2 ≤ 3*W+16 := by
  have hs := BinaryDivisionAllocation.divideStorage_bound dividend divisor W hA hB
  simp only [divideWithTrace,listCells,arraySlots,framePeak]
  exact ⟨by omega,by omega⟩

def trimWithTrace (bits : List Bool) : List Bool×Trace :=
  let result := BinaryRationalOpcodeAllocation.trimWithAllocation bits
  (result.1,[.frames (2*bits.length+8),.arrayAllocation 8,
    .listAllocation (BinaryRationalOpcodeAllocation.trimStorage bits)])

@[simp] theorem trimWithTrace_erases (bits : List Bool) :
    (trimWithTrace bits).1=BinaryCanonicalMagnitude.trim bits :=
  BinaryRationalOpcodeAllocation.trimWithAllocation_state bits

theorem trimWithTrace_bounds (bits : List Bool) :
    listCells (trimWithTrace bits).2+arraySlots (trimWithTrace bits).2 ≤ 8*bits.length+14 ∧
    framePeak (trimWithTrace bits).2 ≤ 2*bits.length+8 := by
  have hs := BinaryRationalOpcodeAllocation.trimStorage_bound bits
  simp only [trimWithTrace,listCells,arraySlots,framePeak]
  exact ⟨by omega,by omega⟩

theorem prefix_heap (trace : Trace) (B borrowedCells steps : ℕ)
    (h : listCells trace+arraySlots trace≤B) : retainedHeap borrowedCells trace steps≤borrowedCells+B := by
  have hl := listCells_take_le trace steps
  have ha := arraySlots_take_le trace steps
  unfold retainedHeap
  omega

theorem divide_all_prefix (dividend divisor : List Bool) (W : ℕ)
    (hA : dividend.length≤W) (hB : divisor.length≤W) (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells (divideWithTrace dividend divisor).2 steps≤borrowedCells+500*(W+2)^3+8 := by
  have hb := (divideWithTrace_bounds dividend divisor W hA hB).1
  have hl := listCells_take_le (divideWithTrace dividend divisor).2 steps
  have ha := arraySlots_take_le (divideWithTrace dividend divisor).2 steps
  unfold retainedHeap
  omega

end Blotto.BinaryBooleanPrimitiveLifetime
