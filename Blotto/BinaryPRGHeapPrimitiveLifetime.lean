import Blotto.BinaryPRGHeapPackedStore
import Blotto.BinaryBooleanPrimitiveLifetime

/-! Source allocation observers for the physical Boolean tape primitives.
The returned data agree with the executed measured producer. Every copied
Boolean cell and a conservative fixed record region at each activation stay
retained; inputs and all old versions are borrowed separately. Traces are
ghost evidence, not an additional producer cost or host allocator model. -/

namespace Blotto.BinaryPRGHeapPrimitiveLifetime
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGWordStoreHeapMachine (Charge)
set_option maxHeartbeats 1000000

def cells (trace : Trace) : ℕ := listCells trace + arraySlots trace

@[simp] theorem cells_append (first second : Trace) :
    cells (first ++ second) = cells first + cells second := by simp [cells]; omega

@[simp] theorem cells_under (depth : ℕ) (trace : Trace) :
    cells (under depth trace) = cells trace := by simp [cells]

def price (charge : Charge) : ℕ := 16 * (charge.work + charge.allocatedBits)

def fieldWithTrace : List Bool → List Bool × Trace
  | [] => ([false],[.frames 1,.arrayAllocation 8,.listAllocation 1])
  | bit :: rest =>
      let later := fieldWithTrace rest
      (true :: bit :: later.1,[.frames 1,.arrayAllocation 8,.listAllocation 2] ++ under 1 later.2)

theorem fieldWithTrace_erasure (bits : List Bool) :
    (fieldWithTrace bits).1 = (BinaryPRGWordStoreHeapMachine.fieldWithWork bits).1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [fieldWithTrace,BinaryPRGWordStoreHeapMachine.fieldWithWork,ih]

theorem fieldWithTrace_bound (bits : List Bool) :
    cells (fieldWithTrace bits).2 + 8 ≤ price (BinaryPRGWordStoreHeapMachine.fieldWithWork bits).2 ∧
      framePeak (fieldWithTrace bits).2 ≤ (BinaryPRGWordStoreHeapMachine.fieldWithWork bits).2.work := by
  induction bits with
  | nil => simp [fieldWithTrace,BinaryPRGWordStoreHeapMachine.fieldWithWork,cells,listCells,arraySlots,framePeak,price]
  | cons bit rest ih =>
      have hf := framePeak_under 1 (fieldWithTrace rest).2
      simp only [fieldWithTrace,BinaryPRGWordStoreHeapMachine.fieldWithWork,
        cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at ih ⊢
      exact ⟨by omega,by omega⟩

def readFieldWithTrace : List Bool → Option (List Bool × List Bool) × Trace
  | false :: rest => (some ([],rest),[.frames 1,.arrayAllocation 8])
  | true :: bit :: rest =>
      let later := readFieldWithTrace rest
      (later.1.map (fun parsed => (bit :: parsed.1,parsed.2)),
        [.frames 1,.arrayAllocation 8,.listAllocation 1] ++ under 1 later.2)
  | _ => (none,[.frames 1,.arrayAllocation 8])

theorem readFieldWithTrace_erasure (bits : List Bool) :
    (readFieldWithTrace bits).1 = (BinaryPRGWordStoreHeapMachine.readFieldWithWork bits).1 := by
  induction bits using readFieldWithTrace.induct with
  | case1 rest => rfl
  | case2 bit rest ih => simp only [readFieldWithTrace,BinaryPRGWordStoreHeapMachine.readFieldWithWork,ih]
  | case3 bits hFalse hTrue =>
      cases bits with
      | nil => rfl
      | cons bit rest =>
          cases bit
          · exact False.elim (hFalse rest rfl)
          · cases rest with
            | nil => rfl
            | cons next rest => exact False.elim (hTrue next rest rfl)

theorem readFieldWithTrace_bound (bits : List Bool) :
    cells (readFieldWithTrace bits).2 + 8 ≤ price (BinaryPRGWordStoreHeapMachine.readFieldWithWork bits).2 ∧
      framePeak (readFieldWithTrace bits).2 ≤ (BinaryPRGWordStoreHeapMachine.readFieldWithWork bits).2.work := by
  induction bits using readFieldWithTrace.induct with
  | case1 rest => simp [readFieldWithTrace,BinaryPRGWordStoreHeapMachine.readFieldWithWork,cells,listCells,arraySlots,framePeak,price]
  | case2 bit rest ih =>
      have hf := framePeak_under 1 (readFieldWithTrace rest).2
      simp only [readFieldWithTrace,BinaryPRGWordStoreHeapMachine.readFieldWithWork,
        cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at ih ⊢
      exact ⟨by omega,by omega⟩
  | case3 bits => cases bits <;> simp [readFieldWithTrace,BinaryPRGWordStoreHeapMachine.readFieldWithWork,
      cells,listCells,arraySlots,framePeak,price]

def appendWithTrace : List Bool → List Bool → List Bool × Trace
  | [],suffix => (suffix,[.frames 1,.arrayAllocation 8])
  | bit :: rest,suffix =>
      let later := appendWithTrace rest suffix
      (bit :: later.1,[.frames 1,.arrayAllocation 8,.listAllocation 1] ++ under 1 later.2)

theorem appendWithTrace_erasure (first second : List Bool) :
    (appendWithTrace first second).1 = (BinaryPRGWordStoreHeapMachine.appendWithWork first second).1 := by
  induction first with
  | nil => rfl
  | cons bit rest ih => simp only [appendWithTrace,BinaryPRGWordStoreHeapMachine.appendWithWork,ih]

theorem appendWithTrace_bound (first second : List Bool) :
    cells (appendWithTrace first second).2 + 8 ≤ price (BinaryPRGWordStoreHeapMachine.appendWithWork first second).2 ∧
      framePeak (appendWithTrace first second).2 ≤ (BinaryPRGWordStoreHeapMachine.appendWithWork first second).2.work := by
  induction first with
  | nil => simp [appendWithTrace,BinaryPRGWordStoreHeapMachine.appendWithWork,cells,listCells,arraySlots,framePeak,price]
  | cons bit rest ih =>
      have hf := framePeak_under 1 (appendWithTrace rest second).2
      simp only [appendWithTrace,BinaryPRGWordStoreHeapMachine.appendWithWork,
        cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at ih ⊢
      exact ⟨by omega,by omega⟩

def predecessorWithTrace : List Bool → List Bool × Trace
  | [] => ([],[.frames 1,.arrayAllocation 8])
  | true :: rest => (false :: rest,[.frames 1,.arrayAllocation 8,.listAllocation 1])
  | false :: rest =>
      let later := predecessorWithTrace rest
      (true :: later.1,[.frames 1,.arrayAllocation 8,.listAllocation 1] ++ under 1 later.2)

theorem predecessorWithTrace_erasure (bits : List Bool) :
    (predecessorWithTrace bits).1 = BinaryStoredCountdown.predecessor bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [predecessorWithTrace,BinaryStoredCountdown.predecessor,ih]

theorem predecessorWithTrace_bound (bits : List Bool) :
    cells (predecessorWithTrace bits).2 ≤ 9 * (bits.length + 1) ∧
      framePeak (predecessorWithTrace bits).2 ≤ bits.length + 1 := by
  induction bits with
  | nil => simp [predecessorWithTrace,cells,listCells,arraySlots,framePeak]
  | cons bit rest ih =>
      have hf := framePeak_under 1 (predecessorWithTrace rest).2
      simp only [cells] at ih
      cases bit <;> simp only [predecessorWithTrace,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,
        framePeak_append,framePeak,List.length_cons] <;> exact ⟨by omega,by omega⟩

def skipWithTrace (tape : List Bool) (pointer : Pointer) : List Bool × Trace :=
  let tested := BinaryBooleanPrimitiveLifetime.scanWithTrace pointer
  if tested.1 then
    match tape with
    | [] => ([],[.frames 2,.arrayAllocation 8] ++ under 1 tested.2)
    | _ :: rest =>
        let decremented := predecessorWithTrace pointer
        let later := skipWithTrace rest decremented.1
        (later.1,[.frames 2,.arrayAllocation 8] ++ under 1 tested.2 ++ under 1 decremented.2 ++ under 1 later.2)
  else (tape,[.frames 2,.arrayAllocation 8] ++ under 1 tested.2)
termination_by tape.length

theorem skipWithTrace_erasure (tape : List Bool) (pointer : Pointer) :
    (skipWithTrace tape pointer).1 = (BinaryPRGWordStoreHeapMachine.skipWithWork tape pointer).1 := by
  induction tape generalizing pointer with
  | nil =>
      by_cases hn : BinaryEuclideanGCD.nonzero pointer = true <;>
        simp only [skipWithTrace,BinaryPRGWordStoreHeapMachine.skipWithWork,
          BinaryBooleanPrimitiveLifetime.scanWithTrace_erases,BinaryStoredCountdown.nonzeroWithWork,
          hn,Bool.false_eq_true,ite_true,ite_false]
  | cons bit rest ih =>
      by_cases hn : BinaryEuclideanGCD.nonzero pointer = true <;>
        simp only [skipWithTrace,BinaryPRGWordStoreHeapMachine.skipWithWork,
          BinaryBooleanPrimitiveLifetime.scanWithTrace_erases,BinaryStoredCountdown.nonzeroWithWork,
          hn,Bool.false_eq_true,ite_true,ite_false,predecessorWithTrace_erasure,
          BinaryStoredCountdown.predecessorWithWork_state,ih]

theorem skipWithTrace_bound (tape : List Bool) (pointer : Pointer) :
    cells (skipWithTrace tape pointer).2 + 8 ≤ price (BinaryPRGWordStoreHeapMachine.skipWithWork tape pointer).2 ∧
      framePeak (skipWithTrace tape pointer).2 ≤ (BinaryPRGWordStoreHeapMachine.skipWithWork tape pointer).2.work + 1 := by
  induction tape generalizing pointer with
  | nil =>
      have hs := BinaryBooleanPrimitiveLifetime.scanWithTrace_bounds pointer
      have hf := framePeak_under 1 (BinaryBooleanPrimitiveLifetime.scanWithTrace pointer).2
      by_cases hn : BinaryEuclideanGCD.nonzero pointer = true <;>
        simp only [skipWithTrace,BinaryPRGWordStoreHeapMachine.skipWithWork,
          BinaryBooleanPrimitiveLifetime.scanWithTrace_erases,BinaryStoredCountdown.nonzeroWithWork,
          hn,Bool.false_eq_true,ite_true,ite_false,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
          listCells,arraySlots,framePeak_append,framePeak,price] <;> exact ⟨by omega,by omega⟩
  | cons bit rest ih =>
      have hs := BinaryBooleanPrimitiveLifetime.scanWithTrace_bounds pointer
      have hd := predecessorWithTrace_bound pointer
      have hi := ih (BinaryStoredCountdown.predecessor pointer)
      have hf := framePeak_under 1 (BinaryBooleanPrimitiveLifetime.scanWithTrace pointer).2
      have df := framePeak_under 1 (predecessorWithTrace pointer).2
      have lf := framePeak_under 1 (skipWithTrace rest (BinaryStoredCountdown.predecessor pointer)).2
      simp only [cells,price] at hd hi
      by_cases hn : BinaryEuclideanGCD.nonzero pointer = true <;>
        simp only [skipWithTrace,BinaryPRGWordStoreHeapMachine.skipWithWork,
          BinaryBooleanPrimitiveLifetime.scanWithTrace_erases,BinaryStoredCountdown.nonzeroWithWork,
          predecessorWithTrace_erasure,BinaryStoredCountdown.predecessorWithWork_state,
          hn,Bool.false_eq_true,ite_true,ite_false,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
          listCells,arraySlots,framePeak_append,framePeak,price] <;> exact ⟨by omega,by omega⟩

end Blotto.BinaryPRGHeapPrimitiveLifetime
