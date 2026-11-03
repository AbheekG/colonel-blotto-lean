import Blotto.BinaryPRGHeapPackedStore

/-! Actual consecutive persistent tape writes have one source-derived
reservation across the entire sequence. A single Boolean-pointer width room
bound covers every prefix; repeated squaring of local reservations is avoided.
The resulting heap and measured work are polynomial functions of incoming heap,
write count, address depth and reached word payload. Resource-loop production
of these sequences and complete lifetime/metadata joins remain separate. -/

namespace Blotto.BinaryPRGHeapWriteSequence
open BinaryRationalNormalization BinaryPRGWordStoreHeap
open BinaryPRGWordControllerWordStore (Tree write)
open BinaryPRGWordStoreHeapMachine (Charge patchBound)
open BinaryPRGHeapPackedStore (Packed)

abbrev Change (depth : ℕ) := FixedBinaryWord depth × SignedWord

def logicalWrites {depth : ℕ} (tree : Tree depth) : List (Change depth) → Tree depth
  | [] => tree
  | change :: rest => logicalWrites (write tree change.1 change.2) rest

def executeWithWork {depth : ℕ} (data : Packed depth) :
    (changes : List (Change depth)) → Packed depth × Charge
  | [] => (data,⟨1,0⟩)
  | change :: rest =>
      let current := data.writeWithWork change.1 change.2
      let later := executeWithWork current.1 rest
      (later.1,⟨current.2.work + later.2.work + 4,current.2.allocatedBits + later.2.allocatedBits + 4⟩)

theorem executeWithWork_realizes {depth : ℕ} (data : Packed depth) {tree : Tree depth}
    (h : Realizes data.heap.tape data.root tree) (changes : List (Change depth)) :
    Realizes (executeWithWork data changes).1.heap.tape
      (executeWithWork data changes).1.root (logicalWrites tree changes) := by
  induction changes generalizing data tree with
  | nil => exact h
  | cons change rest ih =>
      simpa only [executeWithWork,logicalWrites] using
        (ih (data.writeWithWork change.1 change.2).1
          (BinaryPRGHeapPackedStore.Packed.writeWithWork_realizes data h change.1 change.2))

def payloadCost {depth : ℕ} (change : Change depth) : ℕ :=
  depth + 1 + change.2.numerator.length + change.2.denominator.length

def totalPayload {depth : ℕ} (changes : List (Change depth)) : ℕ := (changes.map payloadCost).sum

def range {depth : ℕ} (data : Packed depth) (changes : List (Change depth)) (P : ℕ) : ℕ :=
  data.heap.tape.length + totalPayload changes * (4 * P + 5)

set_option maxHeartbeats 1000000 in
theorem executeWithWork_controlled {depth : ℕ} (data : Packed depth)
    (changes : List (Change depth)) (P : ℕ) (hP : 0 < P) (hRoom : range data changes P < 2^P) :
    (executeWithWork data changes).1.heap.tape.length ≤ range data changes P ∧
      (executeWithWork data changes).2.work ≤ changes.length * (patchBound (range data changes P) depth + 4) + 1 ∧
      (executeWithWork data changes).2.allocatedBits ≤ changes.length * (patchBound (range data changes P) depth + 4) := by
  induction changes generalizing data with
  | nil => simp [executeWithWork,range,totalPayload]
  | cons change rest ih =>
      let current := data.writeWithWork change.1 change.2
      let B := range data (change :: rest) P
      have hRange : B = data.heap.tape.length + (payloadCost change + totalPayload rest) * (4 * P + 5) := by
        simp only [B,range,totalPayload,List.map_cons,List.sum_cons]
      have hStepRoom : data.heap.tape.length + payloadCost change * (4 * P + 5) < 2^P := by
        simp only [payloadCost] at *
        nlinarith
      have hc := BinaryPRGHeapPackedStore.Packed.writeWithWork_controlled data change.1 change.2 P hP (by simpa only [payloadCost] using hStepRoom)
      have hRemaining : range current.1 rest P ≤ B := by
        change current.1.heap.tape.length + totalPayload rest * (4 * P + 5) ≤ B
        unfold payloadCost at hRange
        nlinarith [hc.1]
      have hl := ih current.1 (hRemaining.trans_lt hRoom)
      have hm := BinaryPRGHeapStoredTree.patchBound_mono hRemaining depth
      have hStep : data.heap.tape.length + payloadCost change * (4 * P + 5) ≤ B := by
        simp only [payloadCost] at *
        nlinarith
      have hs := BinaryPRGHeapStoredTree.patchBound_mono (by simpa only [payloadCost] using hStep) depth
      have hWork := hl.2.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left rest.length (Nat.add_le_add_right hm 4)) 1)
      have hAllocation := hl.2.2.trans (Nat.mul_le_mul_left rest.length (Nat.add_le_add_right hm 4))
      change (executeWithWork current.1 rest).1.heap.tape.length ≤ B ∧
        current.2.work + (executeWithWork current.1 rest).2.work + 4 ≤
          (rest.length + 1) * (patchBound B depth + 4) + 1 ∧
        current.2.allocatedBits + (executeWithWork current.1 rest).2.allocatedBits + 4 ≤
          (rest.length + 1) * (patchBound B depth + 4)
      exact ⟨hl.1.trans hRemaining,by nlinarith [hc.2.1],by nlinarith [hc.2.2]⟩

def sourceSize {depth : ℕ} (data : Packed depth) (changes : List (Change depth)) : ℕ :=
  data.heap.tape.length + totalPayload changes

theorem source_room {depth : ℕ} (data : Packed depth) (changes : List (Change depth)) :
    range data changes (sourceSize data changes + 10) ≤ heapBound (sourceSize data changes) := by
  unfold range sourceSize heapBound
  nlinarith

theorem executeWithWork_source {depth : ℕ} (data : Packed depth) (changes : List (Change depth)) :
    (executeWithWork data changes).1.heap.tape.length ≤ heapBound (sourceSize data changes) ∧
      (executeWithWork data changes).2.work ≤ changes.length * (patchBound (heapBound (sourceSize data changes)) depth + 4) + 1 ∧
      (executeWithWork data changes).2.allocatedBits ≤ changes.length * (patchBound (heapBound (sourceSize data changes)) depth + 4) := by
  have hRoom := (source_room data changes).trans_lt (quadratic_lt_capacity (sourceSize data changes))
  have h := executeWithWork_controlled data changes (sourceSize data changes + 10) (by omega) hRoom
  have hm := BinaryPRGHeapStoredTree.patchBound_mono (source_room data changes) depth
  exact ⟨h.1.trans (source_room data changes),
    h.2.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left changes.length (Nat.add_le_add_right hm 4)) 1),
    h.2.2.trans (Nat.mul_le_mul_left changes.length (Nat.add_le_add_right hm 4))⟩

end Blotto.BinaryPRGHeapWriteSequence
