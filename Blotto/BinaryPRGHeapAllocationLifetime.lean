import Blotto.BinaryPRGHeapPrimitiveLifetime
import Blotto.BinaryWordStoreLifetime

/-! The physical tape parser, encoder, counters and allocator retain all
primitive copies and old versions in source allocation traces. -/

namespace Blotto.BinaryPRGHeapAllocationLifetime
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGHeapPrimitiveLifetime
set_option maxHeartbeats 1000000

def decodeWithTrace : List Bool → Option Cell × Trace
  | false :: negative :: rest =>
      let first := readFieldWithTrace rest
      match first.1 with
      | none => (none,[.frames 2,.arrayAllocation 8] ++ under 1 first.2)
      | some parsed =>
          let second := readFieldWithTrace parsed.2
          (second.1.map (fun later => .leaf ⟨negative,parsed.1,later.1⟩),
            [.frames 2,.arrayAllocation 16] ++ under 1 first.2 ++ under 1 second.2)
  | true :: rest =>
      let first := readFieldWithTrace rest
      match first.1 with
      | none => (none,[.frames 2,.arrayAllocation 8] ++ under 1 first.2)
      | some parsed =>
          let second := readFieldWithTrace parsed.2
          (second.1.map (fun later => .branch parsed.1 later.1),
            [.frames 2,.arrayAllocation 16] ++ under 1 first.2 ++ under 1 second.2)
  | _ => (none,[.frames 1,.arrayAllocation 8])

theorem decodeWithTrace_erasure (bits : List Bool) :
    (decodeWithTrace bits).1 = (BinaryPRGWordStoreHeapMachine.decodeWithWork bits).1 := by
  cases bits with
  | nil => rfl
  | cons first rest =>
      cases first
      · cases rest with
        | nil => rfl
        | cons negative rest => simp only [decodeWithTrace,BinaryPRGWordStoreHeapMachine.decodeWithWork,
            readFieldWithTrace_erasure]; split <;> rename_i hParsed <;> simp only [hParsed]
      · simp only [decodeWithTrace,BinaryPRGWordStoreHeapMachine.decodeWithWork,readFieldWithTrace_erasure]
        split <;> rename_i hParsed <;> simp only [hParsed]

theorem decodeWithTrace_bound (bits : List Bool) :
    cells (decodeWithTrace bits).2 + 8 ≤ price (BinaryPRGWordStoreHeapMachine.decodeWithWork bits).2 ∧
      framePeak (decodeWithTrace bits).2 ≤ (BinaryPRGWordStoreHeapMachine.decodeWithWork bits).2.work := by
  cases bits with
  | nil => simp [decodeWithTrace,BinaryPRGWordStoreHeapMachine.decodeWithWork,cells,listCells,arraySlots,framePeak,price]
  | cons first rest =>
      have hFirst := readFieldWithTrace_bound rest
      have fFirst := framePeak_under 1 (readFieldWithTrace rest).2
      cases first
      · cases rest with
        | nil => simp [decodeWithTrace,BinaryPRGWordStoreHeapMachine.decodeWithWork,cells,listCells,arraySlots,framePeak,price]
        | cons negative rest =>
            have hFirst := readFieldWithTrace_bound rest
            have fFirst := framePeak_under 1 (readFieldWithTrace rest).2
            unfold decodeWithTrace BinaryPRGWordStoreHeapMachine.decodeWithWork
            dsimp only
            simp only [readFieldWithTrace_erasure]
            split
            · rename_i hParsed
              simp only [hParsed]
              simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
                listCells,arraySlots,framePeak_append,framePeak,price] at hFirst ⊢
              exact ⟨by omega,by omega⟩
            · rename_i parsed hParsed
              simp only [hParsed]
              have hSecond := readFieldWithTrace_bound parsed.2
              have fSecond := framePeak_under 1 (readFieldWithTrace parsed.2).2
              simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
                listCells,arraySlots,framePeak_append,framePeak,price] at hFirst hSecond ⊢
              exact ⟨by omega,by omega⟩
      · unfold decodeWithTrace BinaryPRGWordStoreHeapMachine.decodeWithWork
        dsimp only
        simp only [readFieldWithTrace_erasure]
        split
        · rename_i hParsed
          simp only [hParsed]
          simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
            listCells,arraySlots,framePeak_append,framePeak,price] at hFirst ⊢
          exact ⟨by omega,by omega⟩
        · rename_i parsed hParsed
          simp only [hParsed]
          have hSecond := readFieldWithTrace_bound parsed.2
          have fSecond := framePeak_under 1 (readFieldWithTrace parsed.2).2
          simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
            listCells,arraySlots,framePeak_append,framePeak,price] at hFirst hSecond ⊢
          exact ⟨by omega,by omega⟩

def readWithTrace (tape : List Bool) (pointer : Pointer) : Option Cell × Trace :=
  let reached := skipWithTrace tape pointer
  let parsed := decodeWithTrace reached.1
  (parsed.1,[.frames 2,.arrayAllocation 8] ++ under 1 reached.2 ++ under 1 parsed.2)

theorem readWithTrace_erasure (tape : List Bool) (pointer : Pointer) :
    (readWithTrace tape pointer).1 = (BinaryPRGWordStoreHeapMachine.readWithWork tape pointer).1 := by
  simp only [readWithTrace,BinaryPRGWordStoreHeapMachine.readWithWork,skipWithTrace_erasure,decodeWithTrace_erasure]

theorem readWithTrace_bound (tape : List Bool) (pointer : Pointer) :
    cells (readWithTrace tape pointer).2 + 8 ≤ price (BinaryPRGWordStoreHeapMachine.readWithWork tape pointer).2 ∧
      framePeak (readWithTrace tape pointer).2 ≤ (BinaryPRGWordStoreHeapMachine.readWithWork tape pointer).2.work + 3 := by
  have hs := skipWithTrace_bound tape pointer
  have hd := decodeWithTrace_bound (BinaryPRGWordStoreHeapMachine.skipWithWork tape pointer).1
  have sf := framePeak_under 1 (skipWithTrace tape pointer).2
  have df := framePeak_under 1 (decodeWithTrace (BinaryPRGWordStoreHeapMachine.skipWithWork tape pointer).1).2
  simp only [readWithTrace,BinaryPRGWordStoreHeapMachine.readWithWork,skipWithTrace_erasure,
    BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak,price] at hs hd ⊢
  exact ⟨by omega,by omega⟩

def encodeWithTrace : Cell → List Bool × Trace
  | .leaf word =>
      let first := fieldWithTrace word.numerator
      let second := fieldWithTrace word.denominator
      let joined := appendWithTrace first.1 second.1
      (false :: word.negative :: joined.1,[.frames 2,.arrayAllocation 8,.listAllocation 2] ++
        under 1 first.2 ++ under 1 second.2 ++ under 1 joined.2)
  | .branch left right =>
      let first := fieldWithTrace left
      let second := fieldWithTrace right
      let joined := appendWithTrace first.1 second.1
      (true :: joined.1,[.frames 2,.arrayAllocation 8,.listAllocation 1] ++
        under 1 first.2 ++ under 1 second.2 ++ under 1 joined.2)

theorem encodeWithTrace_erasure (cell : Cell) :
    (encodeWithTrace cell).1 = (BinaryPRGWordStoreHeapMachine.encodeWithWork cell).1 := by
  cases cell <;> simp only [encodeWithTrace,BinaryPRGWordStoreHeapMachine.encodeWithWork,
    fieldWithTrace_erasure,appendWithTrace_erasure]

theorem encodeWithTrace_bound (cell : Cell) :
    cells (encodeWithTrace cell).2 + 8 ≤ price (BinaryPRGWordStoreHeapMachine.encodeWithWork cell).2 ∧
      framePeak (encodeWithTrace cell).2 ≤ (BinaryPRGWordStoreHeapMachine.encodeWithWork cell).2.work := by
  cases cell with
  | leaf word =>
      have hA := fieldWithTrace_bound word.numerator
      have hB := fieldWithTrace_bound word.denominator
      have hC := appendWithTrace_bound (BinaryPRGWordStoreHeapMachine.fieldWithWork word.numerator).1
        (BinaryPRGWordStoreHeapMachine.fieldWithWork word.denominator).1
      have fA := framePeak_under 1 (fieldWithTrace word.numerator).2
      have fB := framePeak_under 1 (fieldWithTrace word.denominator).2
      have fC := framePeak_under 1 (appendWithTrace (BinaryPRGWordStoreHeapMachine.fieldWithWork word.numerator).1
        (BinaryPRGWordStoreHeapMachine.fieldWithWork word.denominator).1).2
      simp only [encodeWithTrace,BinaryPRGWordStoreHeapMachine.encodeWithWork,fieldWithTrace_erasure,
        cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,
        framePeak_append,framePeak,price] at hA hB hC ⊢
      exact ⟨by omega,by omega⟩
  | branch left right =>
      have hA := fieldWithTrace_bound left
      have hB := fieldWithTrace_bound right
      have hC := appendWithTrace_bound (BinaryPRGWordStoreHeapMachine.fieldWithWork left).1
        (BinaryPRGWordStoreHeapMachine.fieldWithWork right).1
      have fA := framePeak_under 1 (fieldWithTrace left).2
      have fB := framePeak_under 1 (fieldWithTrace right).2
      have fC := framePeak_under 1 (appendWithTrace (BinaryPRGWordStoreHeapMachine.fieldWithWork left).1
        (BinaryPRGWordStoreHeapMachine.fieldWithWork right).1).2
      simp only [encodeWithTrace,BinaryPRGWordStoreHeapMachine.encodeWithWork,fieldWithTrace_erasure,
        cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,
        framePeak_append,framePeak,price] at hA hB hC ⊢
      exact ⟨by omega,by omega⟩

def countWithTrace {α : Type*} : List α → Pointer → Pointer × Trace
  | [],counter => (counter,[.frames 1,.arrayAllocation 8])
  | _ :: rest,counter =>
      let advanced := BinaryWordStoreLifetime.carryWithTrace counter
      let later := countWithTrace rest advanced.1
      (later.1,[.frames 2,.arrayAllocation 8] ++ under 1 advanced.2 ++ under 1 later.2)

theorem countWithTrace_erasure {α : Type*} (items : List α) (counter : Pointer) :
    (countWithTrace items counter).1 = (BinaryPRGWordStoreHeapMachine.countWithWork items counter).1 := by
  induction items generalizing counter with
  | nil => rfl
  | cons item rest ih => simp only [countWithTrace,BinaryPRGWordStoreHeapMachine.countWithWork,
      BinaryWordStoreLifetime.carryWithTrace_erases,ih]

theorem countWithTrace_bound {α : Type*} (items : List α) (counter : Pointer) :
    cells (countWithTrace items counter).2 + 8 ≤ price (BinaryPRGWordStoreHeapMachine.countWithWork items counter).2 ∧
      framePeak (countWithTrace items counter).2 ≤ (BinaryPRGWordStoreHeapMachine.countWithWork items counter).2.work := by
  induction items generalizing counter with
  | nil => simp [countWithTrace,BinaryPRGWordStoreHeapMachine.countWithWork,cells,listCells,arraySlots,framePeak,price]
  | cons item rest ih =>
      have hCarry := BinaryWordStoreLifetime.carryWithTrace_bounds counter
      have hLater := ih (BinaryCarryCounter.increment counter)
      have fCarry := framePeak_under 1 (BinaryWordStoreLifetime.carryWithTrace counter).2
      have fLater := framePeak_under 1 (countWithTrace rest (BinaryCarryCounter.increment counter)).2
      simp only [countWithTrace,BinaryPRGWordStoreHeapMachine.countWithWork,
        BinaryWordStoreLifetime.carryWithTrace_erases,cells,listCells_append,arraySlots_append,
        listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hLater ⊢
      exact ⟨by omega,by omega⟩

def allocateWithTrace (heap : Heap) (cell : Cell) : (Pointer × Heap) × Trace :=
  let encoded := encodeWithTrace cell
  let written := appendWithTrace heap.tape encoded.1
  let advanced := countWithTrace encoded.1 heap.next
  ((heap.next,⟨written.1,advanced.1⟩),[.frames 2,.arrayAllocation 16] ++
    under 1 encoded.2 ++ under 1 written.2 ++ under 1 advanced.2)

theorem allocateWithTrace_erasure (heap : Heap) (cell : Cell) :
    (allocateWithTrace heap cell).1 = (BinaryPRGWordStoreHeapMachine.allocateWithWork heap cell).1 := by
  simp only [allocateWithTrace,BinaryPRGWordStoreHeapMachine.allocateWithWork,
    encodeWithTrace_erasure,appendWithTrace_erasure,countWithTrace_erasure]

theorem allocateWithTrace_bound (heap : Heap) (cell : Cell) :
    cells (allocateWithTrace heap cell).2 + 8 ≤ price (BinaryPRGWordStoreHeapMachine.allocateWithWork heap cell).2 ∧
      framePeak (allocateWithTrace heap cell).2 ≤ (BinaryPRGWordStoreHeapMachine.allocateWithWork heap cell).2.work := by
  have hE := encodeWithTrace_bound cell
  have hW := appendWithTrace_bound heap.tape (BinaryPRGWordStoreHeapMachine.encodeWithWork cell).1
  have hA := countWithTrace_bound (BinaryPRGWordStoreHeapMachine.encodeWithWork cell).1 heap.next
  have fE := framePeak_under 1 (encodeWithTrace cell).2
  have fW := framePeak_under 1 (appendWithTrace heap.tape (BinaryPRGWordStoreHeapMachine.encodeWithWork cell).1).2
  have fA := framePeak_under 1 (countWithTrace (BinaryPRGWordStoreHeapMachine.encodeWithWork cell).1 heap.next).2
  simp only [allocateWithTrace,BinaryPRGWordStoreHeapMachine.allocateWithWork,encodeWithTrace_erasure,
    cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,
    framePeak_append,framePeak,price] at hE hW hA ⊢
  exact ⟨by omega,by omega⟩

theorem allocate_all_prefix (heap : Heap) (cell : Cell) (hHeap : Valid heap) (B : ℕ)
    (hTape : heap.tape.length + (encode cell).length ≤ B) (borrowed steps : ℕ) :
    retainedHeap borrowed (allocateWithTrace heap cell).2 steps ≤
        borrowed + 32 * BinaryPRGWordStoreHeapMachine.allocationBound B ∧
      framePeak ((allocateWithTrace heap cell).2.take steps) ≤
        BinaryPRGWordStoreHeapMachine.allocationBound B := by
  have hTrace := allocateWithTrace_bound heap cell
  have hCharge := BinaryPRGWordStoreHeapMachine.allocateWithWork_bounds heap cell hHeap B hTape
  have hPrefix := BinaryBooleanPrimitiveLifetime.prefix_heap (allocateWithTrace heap cell).2
    (32 * BinaryPRGWordStoreHeapMachine.allocationBound B) borrowed steps
  have hCells : listCells (allocateWithTrace heap cell).2 + arraySlots (allocateWithTrace heap cell).2 ≤
      32 * BinaryPRGWordStoreHeapMachine.allocationBound B := by
    simp only [cells,price] at hTrace
    omega
  exact ⟨hPrefix hCells,(framePeak_take_le _ _).trans (hTrace.2.trans hCharge.1)⟩

end Blotto.BinaryPRGHeapAllocationLifetime
