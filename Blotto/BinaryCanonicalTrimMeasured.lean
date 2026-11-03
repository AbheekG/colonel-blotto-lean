import Blotto.BinaryBooleanPrimitiveLifetime

/-! Reverse/drop/reverse canonical trimming carries the reached scan count and
allocation frames together. The selected trace now consumes the actual returned
buffers for storage too, without rerunning trimStorage. Native evaluation of
trace/length/allocation observers remains separate. -/

namespace Blotto.BinaryCanonicalTrimMeasured
open BinarySeedPreparationSpace
set_option autoImplicit false

def scan : List Bool → (List Bool × ℕ) × ℕ
  | [] => (([],1),1)
  | true::rest => ((true::rest,1),1)
  | false::rest =>
      let later := scan rest
      ((later.1.1,1+later.1.2),1+later.2)

theorem scan_erases (bits : List Bool) :
    (scan bits).1 = BinaryRationalOpcodeAllocation.trimBigWithFrames bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [scan,BinaryRationalOpcodeAllocation.trimBigWithFrames,ih]

theorem scan_visits (bits : List Bool) : (scan bits).2 = BinaryCanonicalMagnitude.scanVisits bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [scan,BinaryCanonicalMagnitude.scanVisits,
      Bool.false_eq_true,ite_false,ite_true,ih]

def trim (bits : List Bool) : (List Bool × ℕ) × ℕ :=
  let scanned := scan bits.reverse
  ((scanned.1.1.reverse,bits.length+scanned.1.1.length+scanned.1.2+2),
    2*bits.length+3*scanned.2+2*scanned.1.1.length+2)

theorem trim_erases (bits : List Bool) :
    (trim bits).1 = BinaryRationalOpcodeAllocation.trimWithAllocation bits := by
  simp only [trim,BinaryRationalOpcodeAllocation.trimWithAllocation,scan_erases]

theorem trim_data (bits : List Bool) :
    (trim bits).1.1 = (BinaryCanonicalMagnitude.trimWithWork bits).1 := by
  rw [trim_erases,BinaryRationalOpcodeAllocation.trimWithAllocation_state]
  rfl

theorem trim_work (bits : List Bool) :
    (trim bits).2 = (BinaryCanonicalMagnitude.trimWithWork bits).2 := by
  simp only [trim,BinaryCanonicalMagnitude.trimWithWork,BinaryCanonicalMagnitude.bitWork,
    scan_visits,scan_erases,BinaryRationalOpcodeAllocation.trimBigWithFrames_state]

def stored (bits : List Bool) : ((List Bool × ℕ) × ℕ) × ℕ :=
  let reversed := bits.reverse
  let scanned := scan reversed
  let output := scanned.1.1.reverse
  let allocated := bits.length+scanned.1.1.length+scanned.1.2+2
  (((output,allocated),2*bits.length+3*scanned.2+2*scanned.1.1.length+2),
    bits.length+reversed.length+scanned.1.1.length+output.length+scanned.1.2+allocated+2)

theorem stored_erases (bits : List Bool) : (stored bits).1 = trim bits := rfl

theorem stored_storage (bits : List Bool) :
    (stored bits).2 = BinaryRationalOpcodeAllocation.trimStorage bits := by
  rw [BinaryRationalOpcodeAllocation.trimStorage,← trim_erases]
  simp only [stored,trim,scan_erases,BinaryRationalOpcodeAllocation.trimBigWithFrames_state,
    BinaryCanonicalMagnitude.trim,List.length_reverse]

theorem stored_storage_bound (bits : List Bool) : (stored bits).2 ≤ 8*bits.length+6 := by
  rw [stored_storage]
  exact BinaryRationalOpcodeAllocation.trimStorage_bound bits

def traced (bits : List Bool) : (List Bool × Trace) × ℕ :=
  let result := stored bits
  ((result.1.1.1,[.frames (2*bits.length+8),.arrayAllocation 8,.listAllocation result.2]),result.1.2)

theorem traced_erases (bits : List Bool) :
    (traced bits).1 = BinaryBooleanPrimitiveLifetime.trimWithTrace bits := by
  simp only [traced,BinaryBooleanPrimitiveLifetime.trimWithTrace,stored_erases,stored_storage,trim_erases]

theorem traced_data (bits : List Bool) :
    (traced bits).1.1 = (BinaryCanonicalMagnitude.trimWithWork bits).1 := by
  change (stored bits).1.1.1 = _
  rw [stored_erases,trim_data]

theorem traced_work (bits : List Bool) :
    (traced bits).2 = (BinaryCanonicalMagnitude.trimWithWork bits).2 := by
  change (stored bits).1.2 = _
  rw [stored_erases,trim_work]

theorem traced_bound (bits : List Bool) : (traced bits).2 ≤ 7*bits.length+5 := by
  rw [traced_work]
  exact BinaryCanonicalMagnitude.bitWork_bound bits

end Blotto.BinaryCanonicalTrimMeasured
