import Blotto.BinaryPRGHeapPackedLifetime

/-! Every-prefix retained allocation for consecutive physical writes, under
one source-derived pointer reservation. Copies of every old tape and decoded
path stay live; caller input regions are counted through the borrowed term. -/

namespace Blotto.BinaryPRGHeapWriteLifetime
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGHeapPrimitiveLifetime BinaryPRGHeapPackedLifetime
open BinaryPRGHeapPackedStore (Packed)
open BinaryPRGHeapWriteSequence (Change payloadCost totalPayload range sourceSize)
set_option maxHeartbeats 1500000

def executeWithTrace {depth : ℕ} (data : Packed depth) : List (Change depth) → Packed depth × Trace
  | [] => (data,[.frames 1,.arrayAllocation 8])
  | change :: rest =>
      let current := writeWithTrace data change.1 change.2
      let later := executeWithTrace current.1 rest
      (later.1,[.frames 2,.arrayAllocation 16] ++ under 1 current.2 ++ under 1 later.2)

theorem executeWithTrace_erasure {depth : ℕ} (data : Packed depth) (changes : List (Change depth)) :
    (executeWithTrace data changes).1 = (BinaryPRGHeapWriteSequence.executeWithWork data changes).1 := by
  induction changes generalizing data with
  | nil => rfl
  | cons change rest ih =>
      simp only [executeWithTrace,BinaryPRGHeapWriteSequence.executeWithWork,writeWithTrace_erasure,ih]

theorem executeWithTrace_controlled {depth : ℕ} (data : Packed depth)
    (changes : List (Change depth)) (P : ℕ) (hP : 0 < P) (hRoom : range data changes P < 2^P) :
    cells (executeWithTrace data changes).2 ≤
        changes.length * (writeReservation (range data changes P) depth + 16) + 8 ∧
      framePeak (executeWithTrace data changes).2 ≤ changes.length +
        BinaryPRGWordStoreHeapMachine.patchBound (range data changes P) depth + depth + 13 := by
  induction changes generalizing data with
  | nil => simp [executeWithTrace,cells,listCells,arraySlots,framePeak]
  | cons change rest ih =>
      let current := data.writeWithWork change.1 change.2
      let B := range data (change :: rest) P
      have hRange : B = data.heap.tape.length + (payloadCost change + totalPayload rest) * (4 * P + 5) := by
        simp only [B,range,totalPayload,List.map_cons,List.sum_cons]
      have hStep : data.heap.tape.length + payloadCost change * (4 * P + 5) ≤ B := by
        nlinarith
      have hWritten := data.writeWithWork_controlled change.1 change.2 P hP (by
        simpa only [payloadCost] using hStep.trans_lt hRoom)
      have hRemaining : range current.1 rest P ≤ B := by
        change current.1.heap.tape.length + totalPayload rest * (4 * P + 5) ≤ B
        unfold payloadCost at hRange
        nlinarith [hWritten.1]
      have hLater := ih current.1 (hRemaining.trans_lt hRoom)
      have hCurrent := writeWithTrace_controlled data change.1 change.2 P B hP
        (by simpa only [payloadCost] using hStep) hRoom
      have hMono := BinaryPRGHeapStoredTree.patchBound_mono hRemaining depth
      have hReservation : writeReservation (range current.1 rest P) depth ≤ writeReservation B depth := by
        unfold writeReservation
        omega
      have hLaterCells := hLater.1.trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left rest.length (Nat.add_le_add_right hReservation 16)) 8)
      have hLaterFrames : framePeak (executeWithTrace current.1 rest).2 ≤
          rest.length + BinaryPRGWordStoreHeapMachine.patchBound B depth + depth + 13 := by omega
      have fCurrent := framePeak_under 1 (writeWithTrace data change.1 change.2).2
      have fLater := framePeak_under 1 (executeWithTrace current.1 rest).2
      simp only [executeWithTrace,writeWithTrace_erasure]
      change cells ([.frames 2,.arrayAllocation 16] ++ under 1 (writeWithTrace data change.1 change.2).2 ++
        under 1 (executeWithTrace current.1 rest).2) ≤ (rest.length + 1) * (writeReservation B depth + 16) + 8 ∧
        framePeak ([.frames 2,.arrayAllocation 16] ++ under 1 (writeWithTrace data change.1 change.2).2 ++
          under 1 (executeWithTrace current.1 rest).2) ≤ rest.length + 1 +
          BinaryPRGWordStoreHeapMachine.patchBound B depth + depth + 13
      simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,
        listCells,arraySlots,framePeak_append,framePeak] at hCurrent hLaterCells ⊢
      exact ⟨by nlinarith,by omega⟩

theorem executeWithTrace_source {depth : ℕ} (data : Packed depth) (changes : List (Change depth)) :
    cells (executeWithTrace data changes).2 ≤
        changes.length * (writeReservation (heapBound (sourceSize data changes)) depth + 16) + 8 ∧
      framePeak (executeWithTrace data changes).2 ≤ changes.length +
        BinaryPRGWordStoreHeapMachine.patchBound (heapBound (sourceSize data changes)) depth + depth + 13 := by
  have hRoom := (BinaryPRGHeapWriteSequence.source_room data changes).trans_lt
    (quadratic_lt_capacity (sourceSize data changes))
  have h := executeWithTrace_controlled data changes (sourceSize data changes + 10) (by omega) hRoom
  have hm := BinaryPRGHeapStoredTree.patchBound_mono (BinaryPRGHeapWriteSequence.source_room data changes) depth
  have hr : writeReservation (range data changes (sourceSize data changes + 10)) depth ≤
      writeReservation (heapBound (sourceSize data changes)) depth := by unfold writeReservation; omega
  exact ⟨h.1.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left changes.length (Nat.add_le_add_right hr 16)) 8),by omega⟩

theorem execute_all_prefix {depth : ℕ} (data : Packed depth) (changes : List (Change depth)) (borrowed steps : ℕ) :
    retainedHeap borrowed (executeWithTrace data changes).2 steps ≤ borrowed +
        changes.length * (writeReservation (heapBound (sourceSize data changes)) depth + 16) + 8 ∧
      framePeak ((executeWithTrace data changes).2.take steps) ≤ changes.length +
        BinaryPRGWordStoreHeapMachine.patchBound (heapBound (sourceSize data changes)) depth + depth + 13 := by
  have h := executeWithTrace_source data changes
  have hPrefix := BinaryBooleanPrimitiveLifetime.prefix_heap (executeWithTrace data changes).2
    (changes.length * (writeReservation (heapBound (sourceSize data changes)) depth + 16) + 8) borrowed steps h.1
  exact ⟨by omega,(framePeak_take_le _ _).trans h.2⟩

theorem selected_twoWrites_all_prefix {depth : ℕ} (data : Packed depth)
    (first second : FixedBinaryWord depth) (chosen other : SignedWord)
    (W P H : ℕ) (hChosen : width chosen ≤ W) (hOther : width other ≤ W)
    (hP : 0 < P)
    (hSpace : data.heap.tape.length + BinaryPRGHeapResourceUpdateBudget.growth depth W P ≤ H)
    (hRoom : H < 2^P) (borrowed steps : ℕ) :
    let trace := (executeWithTrace data [(first,chosen),(second,other)]).2
    retainedHeap borrowed trace steps ≤ borrowed + 2 * (writeReservation H depth + 16) + 8 ∧
      framePeak (trace.take steps) ≤ BinaryPRGWordStoreHeapMachine.patchBound H depth + depth + 15 := by
  let changes : List (Change depth) := [(first,chosen),(second,other)]
  have hcn : chosen.numerator.length ≤ W := (Nat.le_max_left _ _).trans hChosen
  have hcd : chosen.denominator.length ≤ W := (Nat.le_max_right _ _).trans hChosen
  have hon : other.numerator.length ≤ W := (Nat.le_max_left _ _).trans hOther
  have hod : other.denominator.length ≤ W := (Nat.le_max_right _ _).trans hOther
  have hPayload : totalPayload changes ≤ 2 * (depth + 1 + 2 * W) := by
    simp only [changes,totalPayload,payloadCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega
  have hRange : range data changes P ≤ H := by
    apply (Nat.add_le_add_left (Nat.mul_le_mul_right (4 * P + 5) hPayload) data.heap.tape.length).trans
    exact hSpace
  have h := executeWithTrace_controlled data changes P hP (hRange.trans_lt hRoom)
  have hm := BinaryPRGHeapStoredTree.patchBound_mono hRange depth
  have hr : writeReservation (range data changes P) depth ≤ writeReservation H depth := by
    unfold writeReservation
    omega
  have hCells : cells (executeWithTrace data changes).2 ≤ 2 * (writeReservation H depth + 16) + 8 := by
    have hLength : changes.length = 2 := rfl
    rw [hLength] at h
    nlinarith [h.1]
  have hPrefix := BinaryBooleanPrimitiveLifetime.prefix_heap (executeWithTrace data changes).2
    (2 * (writeReservation H depth + 16) + 8) borrowed steps hCells
  have hFrames := (framePeak_take_le (executeWithTrace data changes).2 steps).trans h.2
  change retainedHeap borrowed (executeWithTrace data changes).2 steps ≤ _ ∧
    framePeak ((executeWithTrace data changes).2.take steps) ≤ _
  have hLength : changes.length = 2 := rfl
  rw [hLength] at hFrames
  exact ⟨by omega,by omega⟩

end Blotto.BinaryPRGHeapWriteLifetime
