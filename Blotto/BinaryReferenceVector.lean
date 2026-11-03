import Blotto.BinaryPRGHeapTraceUsage

/-! Physical pointer slots are self-delimited Boolean fields. Indexed reads
parse actual fields and decrement a stored Boolean index; no numerical address
decoder or native array access is used. Prices are those of the existing
Boolean field/scan/borrow primitives, derived from the actual reached tape.
Pointer validity is supplied by the actual object heap in later callers. -/
namespace Blotto.BinaryReferenceVector
open BinaryPRGWordStoreHeap BinaryPRGWordStoreHeapMachine
set_option maxHeartbeats 2000000

def encode : List Pointer → List Bool
  | [] => []
  | pointer::rest => field pointer++encode rest

def payload (pointers : List Pointer) : ℕ := (pointers.map List.length).sum

theorem encode_length (pointers : List Pointer) : (encode pointers).length = 2*payload pointers+pointers.length := by
  induction pointers with
  | nil => rfl
  | cons pointer rest ih => simp only [encode,List.length_append,field_length,payload,List.map_cons,List.sum_cons,List.length_cons] at *; omega

theorem readField_strict (tape : List Bool) (parsed : Pointer × List Bool) (h : readField tape = some parsed) :
    parsed.2.length < tape.length := by
  cases tape with
  | nil => cases h
  | cons tag rest =>
      cases tag
      · cases h
        simp
      · cases rest with
        | nil => cases h
        | cons bit rest =>
            cases hf : readField rest with
            | none => simp only [readField,hf,Option.map_none] at h; cases h
            | some later =>
                simp only [readField,hf,Option.map_some] at h
                cases h
                have hs := readField_suffix rest later hf
                simp only [List.length_cons]
                omega

def readWithWork (tape index : List Bool) : Option Pointer × ℕ :=
  let parsed := readFieldWithWork tape
  match hParsed : parsed.1 with
  | none => (none,parsed.2.work+4)
  | some found =>
      if BinaryEuclideanGCD.nonzero index = true then
        let decremented := BinaryStoredCountdown.predecessorWithWork index
        let later := readWithWork found.2 decremented.1
        (later.1,parsed.2.work+(index.length+1)+decremented.2+later.2+8)
      else (some found.1,parsed.2.work+(index.length+1)+8)
termination_by tape.length
decreasing_by
  apply readField_strict tape found
  change (readFieldWithWork tape).1 = some found at hParsed
  exact (readFieldWithWork_erasure tape).symm.trans hParsed

theorem read_encoded (pointers : List Pointer) (index : List Bool) :
    (readWithWork (encode pointers) index).1 = pointers[BinaryBigEndian.littleValue index]? := by
  induction pointers generalizing index with
  | nil => simp [encode,readWithWork,readFieldWithWork]
  | cons pointer rest ih =>
      rw [readWithWork]
      dsimp only
      have hf : (readFieldWithWork (encode (pointer::rest))).1 = some (pointer,encode rest) := by
        rw [readFieldWithWork_erasure]
        exact readField_field pointer (encode rest)
      rw [hf]
      dsimp only
      by_cases hn : BinaryEuclideanGCD.nonzero index = true
      · rw [ite_eq_left hn]
        rw [BinaryStoredCountdown.predecessorWithWork_state,ih]
        have hd := BinaryStoredCountdown.predecessor_value index ((BinaryEuclideanGCD.nonzero_true_iff index).mp hn)
        rw [← hd]
        simp only [List.getElem?_cons_succ]
      · rw [ite_eq_right hn]
        have hz : BinaryBigEndian.littleValue index = 0 := by
          have h := (BinaryEuclideanGCD.nonzero_true_iff index).not.mp hn
          omega
        simp only [hz,List.getElem?_cons_zero]

def readBound (cells indexWidth : ℕ) : ℕ := 128*(cells+1)*(cells+indexWidth+2)

theorem readWithWork_bound (tape index : List Bool) : (readWithWork tape index).2 ≤ readBound tape.length index.length := by
  have hAll : ∀ length,∀ tape : List Bool,tape.length = length → ∀ index,
      (readWithWork tape index).2 ≤ readBound length index.length := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length ih =>
        intro tape hLength index
        have hField := (readFieldWithWork_bounds tape).1
        rw [readWithWork]
        dsimp only
        split
        · unfold readBound
          nlinarith
        · rename_i found hFound
          have hRead : readField tape = some found := (readFieldWithWork_erasure tape).symm.trans hFound
          have hLess := readField_strict tape found hRead
          split
          · have hLater := ih found.2.length (by omega) found.2 rfl (BinaryStoredCountdown.predecessorWithWork index).1
            have hDec := BinaryStoredCountdown.predecessorWithWork_bound index
            rw [BinaryStoredCountdown.predecessorWithWork_state,BinaryStoredCountdown.predecessor_length] at hLater
            have hProduct : (found.2.length+1)*(found.2.length+index.length+2) ≤ length*(length+index.length+1) := by
              apply Nat.mul_le_mul <;> omega
            rw [BinaryStoredCountdown.predecessorWithWork_state]
            unfold readBound at *
            nlinarith
          · unfold readBound
            nlinarith
  exact hAll _ tape rfl index

theorem payload_bound (pointers : List Pointer) (width : ℕ) (h : ∀ pointer ∈ pointers,pointer.length ≤ width) :
    payload pointers ≤ pointers.length*width := by
  induction pointers with
  | nil => simp [payload]
  | cons pointer rest ih =>
      have hp := h pointer (by simp)
      have hr := ih (fun p hp => h p (by simp [hp]))
      simp only [payload,List.map_cons,List.sum_cons,List.length_cons] at *
      nlinarith

theorem encoded_heap_bound (heap : Heap) (pointers : List Pointer)
    (h : ∀ pointer ∈ pointers,∃ cell,Contains heap.tape pointer cell) :
    (encode pointers).length ≤ pointers.length*(2*binaryWordWidth heap.tape.length+1) := by
  have hWidth : ∀ pointer ∈ pointers,pointer.length ≤ binaryWordWidth heap.tape.length := by
    intro pointer hp
    obtain ⟨cell,hCell⟩ := h pointer hp
    exact contains_pointer_width hCell
  have hp := payload_bound pointers _ hWidth
  rw [encode_length]
  nlinarith

end Blotto.BinaryReferenceVector
