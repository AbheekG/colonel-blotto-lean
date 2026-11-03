import Blotto.BinaryWordObjectArray
import Blotto.BinaryReferenceVectorLifetime

/-! Actual leaf allocations and slot copies produce the physical word array.
Preparation work and every-prefix retained source storage derive from the
incoming words themselves. No final-heap, pointer-width, copy-price or native
array-access oracle is supplied. Word rows remain only in erased proofs. -/
namespace Blotto.BinaryWordObjectArrayLifetime
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinaryWordObjectArray
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000

def encodeWithWork : List Pointer → List Bool × ℕ
  | [] => ([],1)
  | pointer::pointers =>
      let field := BinaryPRGWordStoreHeapMachine.fieldWithWork pointer
      let later := encodeWithWork pointers
      let joined := BinaryPRGWordStoreHeapMachine.appendWithWork field.1 later.1
      (joined.1,field.2.work+later.2+joined.2.work+4)

theorem encodeWithWork_state (pointers : List Pointer) : (encodeWithWork pointers).1 = BinaryReferenceVector.encode pointers := by
  induction pointers with
  | nil => rfl
  | cons pointer rest ih => simp only [encodeWithWork,BinaryReferenceVector.encode,
      BinaryPRGWordStoreHeapMachine.fieldWithWork_erasure,BinaryPRGWordStoreHeapMachine.appendWithWork_erasure,ih]

theorem encodeWithWork_bound (pointers : List Pointer) :
    (encodeWithWork pointers).2 ≤ 16*(BinaryReferenceVector.payload pointers+pointers.length+1) := by
  induction pointers with
  | nil => simp [encodeWithWork,BinaryReferenceVector.payload]
  | cons pointer rest ih =>
      have hField := (BinaryPRGWordStoreHeapMachine.fieldWithWork_price pointer).1
      have hAppend := (BinaryPRGWordStoreHeapMachine.appendWithWork_price
        (BinaryPRGWordStoreHeapMachine.fieldWithWork pointer).1 (encodeWithWork rest).1).1
      have hLength : (BinaryPRGWordStoreHeapMachine.fieldWithWork pointer).1.length = 2*pointer.length+1 := by
        rw [BinaryPRGWordStoreHeapMachine.fieldWithWork_erasure,field_length]
      rw [hLength] at hAppend
      change _+_+_+4 ≤ _
      simp only [BinaryReferenceVector.payload,List.map_cons,List.sum_cons,List.length_cons] at *
      omega

def wordsWithWork (heap : Heap) : List SignedWord → (List Pointer × Heap) × ℕ
  | [] => (([],heap),4)
  | word::words =>
      let allocated := BinaryPRGWordStoreHeapMachine.allocateWithWork heap (.leaf word)
      let later := wordsWithWork allocated.1.2 words
      ((allocated.1.1::later.1.1,later.1.2),allocated.2.work+later.2+8)

theorem wordsWithWork_state (heap : Heap) (words : List SignedWord) :
    (wordsWithWork heap words).1 = allocateWords heap words := by
  induction words generalizing heap with
  | nil => rfl
  | cons word words ih => simp only [wordsWithWork,allocateWords,ih,BinaryPRGWordStoreHeapMachine.allocateWithWork_erasure]

theorem wordsWithWork_bound (heap : Heap) (words : List SignedWord) (hHeap : Valid heap)
    (B : ℕ) (hB : heap.tape.length+payloadBits words ≤ B) :
    (wordsWithWork heap words).2 ≤ words.length*(BinaryPRGWordStoreHeapMachine.allocationBound B+8)+4 := by
  induction words generalizing heap with
  | nil => simp [wordsWithWork]
  | cons word words ih =>
      have hSplit : heap.tape.length+(encode (.leaf word)).length+payloadBits words ≤ B := by
        simpa only [payloadBits,List.map_cons,List.sum_cons,Nat.add_assoc] using hB
      have hOne := (BinaryPRGWordStoreHeapMachine.allocateWithWork_bounds heap (.leaf word) hHeap B (by omega)).1
      have hValid : Valid (BinaryPRGWordStoreHeapMachine.allocateWithWork heap (.leaf word)).1.2 := by
        rw [BinaryPRGWordStoreHeapMachine.allocateWithWork_erasure]
        exact allocate_valid heap (.leaf word) hHeap
      have hRest : (BinaryPRGWordStoreHeapMachine.allocateWithWork heap (.leaf word)).1.2.tape.length+payloadBits words ≤ B := by
        rw [BinaryPRGWordStoreHeapMachine.allocateWithWork_erasure]
        simpa only [allocate,List.length_append] using hSplit
      have hLater := ih _ hValid hRest
      simp only [wordsWithWork,List.length_cons]
      nlinarith

def wordsWithTrace (heap : Heap) : List SignedWord → (List Pointer × Heap) × Trace
  | [] => (([],heap),wrap 8 1 [])
  | word::words =>
      let allocated := BinaryPRGHeapAllocationLifetime.allocateWithTrace heap (.leaf word)
      let later := wordsWithTrace allocated.1.2 words
      ((allocated.1.1::later.1.1,later.1.2),wrapList 1 32 2 [allocated.2,later.2])

theorem allocation_state (heap : Heap) (word : SignedWord) :
    (BinaryPRGHeapAllocationLifetime.allocateWithTrace heap (.leaf word)).1 = allocate heap (.leaf word) := by
  rw [BinaryPRGHeapAllocationLifetime.allocateWithTrace_erasure,BinaryPRGWordStoreHeapMachine.allocateWithWork_erasure]

theorem wordsWithTrace_state (heap : Heap) (words : List SignedWord) : (wordsWithTrace heap words).1 = allocateWords heap words := by
  induction words generalizing heap with
  | nil => rfl
  | cons word words ih => simp only [wordsWithTrace,allocateWords,ih,allocation_state]

theorem allocation_usage (heap : Heap) (word : SignedWord) (hHeap : Valid heap) (B : ℕ)
    (hB : heap.tape.length+(encode (.leaf word)).length ≤ B) :
    usage (BinaryPRGHeapAllocationLifetime.allocateWithTrace heap (.leaf word)).2 ≤
      33*BinaryPRGWordStoreHeapMachine.allocationBound B := by
  have h := BinaryPRGHeapAllocationLifetime.allocateWithTrace_bound heap (.leaf word)
  have hb := BinaryPRGWordStoreHeapMachine.allocateWithWork_bounds heap (.leaf word) hHeap B hB
  unfold usage BinaryPRGHeapPrimitiveLifetime.price at *
  omega

theorem words_usage (heap : Heap) (words : List SignedWord) (hHeap : Valid heap)
    (B : ℕ) (hB : heap.tape.length+payloadBits words ≤ B) :
    usage (wordsWithTrace heap words).2 ≤ words.length*(33*BinaryPRGWordStoreHeapMachine.allocationBound B+64)+16 := by
  induction words generalizing heap with
  | nil => exact (wrap_usage 8 1 []).trans (by simp)
  | cons word words ih =>
      have hSplit : heap.tape.length+(encode (.leaf word)).length+payloadBits words ≤ B := by
        simpa only [payloadBits,List.map_cons,List.sum_cons,Nat.add_assoc] using hB
      have hOne := allocation_usage heap word hHeap B (by omega)
      have hValid : Valid (BinaryPRGHeapAllocationLifetime.allocateWithTrace heap (.leaf word)).1.2 := by
        rw [allocation_state]
        exact allocate_valid heap (.leaf word) hHeap
      have hRest : (BinaryPRGHeapAllocationLifetime.allocateWithTrace heap (.leaf word)).1.2.tape.length+payloadBits words ≤ B := by
        rw [allocation_state]
        simpa only [allocate,List.length_append] using hSplit
      have hLater := ih _ hValid hRest
      have hw := wrapList_usage 1 32 2 [(BinaryPRGHeapAllocationLifetime.allocateWithTrace heap (.leaf word)).2,
        (wordsWithTrace (BinaryPRGHeapAllocationLifetime.allocateWithTrace heap (.leaf word)).1.2 words).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wordsWithTrace heap (word::words)).2 ≤ _ at hw
      simp only [List.length_cons]
      nlinarith

theorem prepared_pointer_payload (words : List SignedWord) :
    BinaryReferenceVector.payload (allocateWords empty words).1 ≤ words.length*binaryWordWidth (payloadBits words) := by
  have h := (allocate_contract empty words empty_valid).2.2.1
  have hWidth : ∀ pointer ∈ (allocateWords empty words).1,pointer.length ≤ binaryWordWidth (payloadBits words) := by
    intro pointer hp
    obtain ⟨word,hWord⟩ := h.contains pointer hp
    have hP := contains_pointer_width hWord
    have hLength := prepare_heap_length words
    change (allocateWords empty words).2.tape.length = _ at hLength
    rwa [hLength] at hP
  have hPayload := BinaryReferenceVector.payload_bound _ _ hWidth
  rw [h.length] at hPayload
  exact hPayload

def prepareWithWork (words : List SignedWord) : Store words.length × ℕ :=
  let allocated := wordsWithWork empty words
  let slots := encodeWithWork allocated.1.1
  have hState := wordsWithWork_state empty words
  have h := allocate_contract empty words empty_valid
  (⟨allocated.1.2,slots.1,(by rw [hState]; exact h.1),
    ⟨allocated.1.1,words,rfl,encodeWithWork_state _,(by rw [hState]; exact h.2.2.1)⟩⟩,
    allocated.2+slots.2+8)

theorem prepareWithWork_state (words : List SignedWord) : (prepareWithWork words).1 = prepare words := by
  apply Store.ext
  · exact congrArg Prod.snd (wordsWithWork_state empty words)
  · simp only [prepareWithWork,BinaryWordObjectArray.prepare,encodeWithWork_state,wordsWithWork_state]

def workEnvelope (words : List SignedWord) : ℕ :=
  words.length*(BinaryPRGWordStoreHeapMachine.allocationBound (payloadBits words)+8)+
    16*(words.length*binaryWordWidth (payloadBits words)+words.length+1)+16

theorem prepareWithWork_bound (words : List SignedWord) : (prepareWithWork words).2 ≤ workEnvelope words := by
  have hw := wordsWithWork_bound empty words empty_valid (payloadBits words) (by simp [empty])
  have he := encodeWithWork_bound (wordsWithWork empty words).1.1
  rw [wordsWithWork_state] at he
  have hp := prepared_pointer_payload words
  have hn := ((allocate_contract empty words empty_valid).2.2.1).length
  change _+_+8 ≤ _
  rw [wordsWithWork_state]
  unfold workEnvelope
  nlinarith

def prepareWithTrace (words : List SignedWord) : Store words.length × Trace :=
  let allocated := wordsWithTrace empty words
  let slots := BinaryReferenceVectorLifetime.encodeWithTrace allocated.1.1
  have hState := wordsWithTrace_state empty words
  have h := allocate_contract empty words empty_valid
  (⟨allocated.1.2,slots.1,(by rw [hState]; exact h.1),
    ⟨allocated.1.1,words,rfl,BinaryReferenceVectorLifetime.encode_state _,(by rw [hState]; exact h.2.2.1)⟩⟩,
    wrap 32 2 [allocated.2,slots.2])

theorem prepareWithTrace_state (words : List SignedWord) : (prepareWithTrace words).1 = prepare words := by
  apply Store.ext
  · exact congrArg Prod.snd (wordsWithTrace_state empty words)
  · simp only [prepareWithTrace,BinaryWordObjectArray.prepare,BinaryReferenceVectorLifetime.encode_state,wordsWithTrace_state]

def envelope (words : List SignedWord) : ℕ :=
  words.length*(33*BinaryPRGWordStoreHeapMachine.allocationBound (payloadBits words)+64)+
    1024*(words.length*binaryWordWidth (payloadBits words)+words.length+1)+128

theorem prepare_usage (words : List SignedWord) : usage (prepareWithTrace words).2 ≤ envelope words := by
  have hw := words_usage empty words empty_valid (payloadBits words) (by simp [empty])
  have he := BinaryReferenceVectorLifetime.encode_usage (wordsWithTrace empty words).1.1
  rw [wordsWithTrace_state] at he
  have hp := prepared_pointer_payload words
  have hn := ((allocate_contract empty words empty_valid).2.2.1).length
  have hWrap := wrap_usage 32 2 [(wordsWithTrace empty words).2,
    (BinaryReferenceVectorLifetime.encodeWithTrace (wordsWithTrace empty words).1.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  change usage (prepareWithTrace words).2 ≤ _ at hWrap
  rw [wordsWithTrace_state] at hWrap
  unfold envelope
  nlinarith

theorem all_prefix (words : List SignedWord) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareWithTrace words).2 steps ≤ borrowed+envelope words ∧
      framePeak ((prepareWithTrace words).2.take steps) ≤ envelope words :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepare_usage words) borrowed steps

end Blotto.BinaryWordObjectArrayLifetime
