import Blotto.BinaryReferenceVector

/-! A word array stores only an actual object heap and a Boolean pointer-slot
tape. Logical rows occur in erased realization proofs, not shadow runtime
arrays. Every leaf is allocated by the existing Boolean counter allocator.
Reads parse the actual selected pointer and then the actual object leaf. -/
namespace Blotto.BinaryWordObjectArray
open BinaryRationalNormalization BinaryPRGWordStoreHeap
set_option maxHeartbeats 2000000

inductive Links (tape : List Bool) : List Pointer → List SignedWord → Prop where
  | nil : Links tape [] []
  | cons {pointer pointers word words} : Contains tape pointer (.leaf word) →
      Links tape pointers words → Links tape (pointer::pointers) (word::words)

theorem Links.extends {old new : Heap} (hExt : Extends new old) {pointers : List Pointer} {words : List SignedWord}
    (h : Links old.tape pointers words) : Links new.tape pointers words := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (contains_extends hExt head) ih

theorem Links.length {tape : List Bool} {pointers : List Pointer} {words : List SignedWord}
    (h : Links tape pointers words) : pointers.length = words.length := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp only [List.length_cons,ih]

theorem Links.contains {tape : List Bool} {pointers : List Pointer} {words : List SignedWord}
    (h : Links tape pointers words) : ∀ pointer ∈ pointers,∃ word,Contains tape pointer (.leaf word) := by
  induction h with
  | nil => simp
  | cons head tail ih =>
      intro pointer hp
      rcases List.mem_cons.mp hp with hp|hp
      · subst pointer
        exact ⟨_,head⟩
      · exact ih pointer hp

def leafRead (tape : List Bool) (pointer : Pointer) : Option SignedWord :=
  match read tape pointer with
  | some (.leaf word) => some word
  | _ => none

theorem Links.read {tape : List Bool} {pointers : List Pointer} {words : List SignedWord}
    (h : Links tape pointers words) (index : ℕ) :
    pointers[index]?.bind (leafRead tape) = words[index]? := by
  induction h generalizing index with
  | nil => rfl
  | cons head tail ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero,Option.bind_some,leafRead,contains_read head]
      | succ index => simpa only [List.getElem?_cons_succ] using ih index

def payloadBits (words : List SignedWord) : ℕ := (words.map (fun word => (encode (.leaf word)).length)).sum

def allocateWords (heap : Heap) : List SignedWord → List Pointer × Heap
  | [] => ([],heap)
  | word::words =>
      let allocated := allocate heap (.leaf word)
      let later := allocateWords allocated.2 words
      (allocated.1::later.1,later.2)

theorem allocate_contract (heap : Heap) (words : List SignedWord) (hHeap : Valid heap) :
    Valid (allocateWords heap words).2 ∧ Extends (allocateWords heap words).2 heap ∧
      Links (allocateWords heap words).2.tape (allocateWords heap words).1 words ∧
      (allocateWords heap words).2.tape.length = heap.tape.length+payloadBits words := by
  induction words generalizing heap with
  | nil => exact ⟨hHeap,extends_refl heap,.nil,rfl⟩
  | cons word words ih =>
      let allocated := allocate heap (.leaf word)
      obtain ⟨hValid,hExt,hLinks,hLength⟩ := ih allocated.2 (allocate_valid heap (.leaf word) hHeap)
      have hHead := contains_extends hExt (allocate_contains heap (.leaf word) hHeap)
      refine ⟨hValid,extends_trans hExt (allocate_extends heap (.leaf word)),.cons hHead hLinks,?_⟩
      change (allocateWords allocated.2 words).2.tape.length = _
      rw [hLength]
      simp only [allocated,allocate,payloadBits,List.length_append,List.map_cons,List.sum_cons]
      omega

theorem payloadBits_bound (words : List SignedWord) (W : ℕ) (h : ∀ word ∈ words,width word ≤ W) :
    payloadBits words ≤ 4*words.length*(W+1) := by
  induction words with
  | nil => simp [payloadBits]
  | cons word words ih =>
      have hw := h word (by simp)
      have hRest := ih (fun w hw => h w (by simp [hw]))
      unfold width at hw
      have hn := (Nat.le_max_left word.numerator.length word.denominator.length).trans hw
      have hd := (Nat.le_max_right word.numerator.length word.denominator.length).trans hw
      simp only [payloadBits,List.map_cons,List.sum_cons,encode_leaf_length,List.length_cons] at *
      nlinarith

structure Store (n : ℕ) where
  heap : Heap
  slots : List Bool
  valid : Valid heap
  realized : ∃ pointers words,words.length = n ∧ slots = BinaryReferenceVector.encode pointers ∧ Links heap.tape pointers words

theorem Store.ext {n : ℕ} (first second : Store n) (hHeap : first.heap = second.heap) (hSlots : first.slots = second.slots) :
    first = second := by
  cases first
  cases second
  cases hHeap
  cases hSlots
  rfl

def Store.Realizes {n : ℕ} (store : Store n) (words : List SignedWord) : Prop :=
  ∃ pointers,store.slots = BinaryReferenceVector.encode pointers ∧ Links store.heap.tape pointers words

def prepare (words : List SignedWord) : Store words.length :=
  let allocated := allocateWords empty words
  let h := allocate_contract empty words empty_valid
  ⟨allocated.2,BinaryReferenceVector.encode allocated.1,h.1,⟨allocated.1,words,rfl,rfl,h.2.2.1⟩⟩

theorem prepare_realizes (words : List SignedWord) : (prepare words).Realizes words :=
  ⟨(allocateWords empty words).1,rfl,(allocate_contract empty words empty_valid).2.2.1⟩

theorem prepare_heap_length (words : List SignedWord) : (prepare words).heap.tape.length = payloadBits words := by
  simpa only [prepare,empty,List.length_nil,Nat.zero_add] using (allocate_contract empty words empty_valid).2.2.2

theorem Store.slots_bound {n : ℕ} (store : Store n) :
    store.slots.length ≤ n*(2*binaryWordWidth store.heap.tape.length+1) := by
  obtain ⟨pointers,words,hLength,hSlots,hLinks⟩ := store.realized
  rw [hSlots]
  have h := BinaryReferenceVector.encoded_heap_bound store.heap pointers (by
    intro pointer hp
    obtain ⟨word,hw⟩ := hLinks.contains pointer hp
    exact ⟨.leaf word,hw⟩)
  rw [hLinks.length,hLength] at h
  exact h

def get {n : ℕ} (store : Store n) (index : List Bool) : Option SignedWord :=
  (BinaryReferenceVector.readWithWork store.slots index).1.bind (leafRead store.heap.tape)

theorem get_state {n : ℕ} (store : Store n) (words : List SignedWord) (h : store.Realizes words) (index : List Bool) :
    get store index = words[BinaryBigEndian.littleValue index]? := by
  obtain ⟨pointers,hSlots,hLinks⟩ := h
  rw [get,hSlots,BinaryReferenceVector.read_encoded]
  exact hLinks.read _

theorem get_prepare (words : List SignedWord) (index : List Bool) :
    get (prepare words) index = words[BinaryBigEndian.littleValue index]? := get_state _ _ (prepare_realizes words) index

theorem getElemOption_mem {α : Type*} (items : List α) (index : ℕ) (value : α) (h : items[index]? = some value) : value ∈ items := by
  induction items generalizing index with
  | nil => cases h
  | cons item rest ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at h; subst value; simp
      | succ index => exact List.mem_cons_of_mem _ (ih index h)

theorem Links.words_width_le_tape {tape : List Bool}
    {pointers : List Pointer} {words : List SignedWord}
    (h : Links tape pointers words) :
    ∀ word ∈ words,width word ≤ tape.length := by
  induction h with
  | nil => simp
  | @cons pointer pointers word words head tail ih =>
      intro item hItem
      rcases List.mem_cons.mp hItem with hEq | hRest
      · subst item
        obtain ⟨beforeBits,suffix,hTape,_⟩ := head
        have hLength : (encode (.leaf word)).length ≤ tape.length := by
          rw [hTape]
          simp only [List.length_append]
          omega
        rw [encode_leaf_length] at hLength
        unfold width
        omega
      · exact ih item hRest

theorem get_width_le_tape {n : ℕ} (store : Store n)
    (index : List Bool) (word : SignedWord)
    (hRead : get store index = some word) :
    width word ≤ store.heap.tape.length := by
  obtain ⟨pointers,words,hLength,hSlots,hLinks⟩ := store.realized
  have hRealizes : store.Realizes words := ⟨pointers,hSlots,hLinks⟩
  rw [get_state store words hRealizes] at hRead
  exact hLinks.words_width_le_tape word
    (getElemOption_mem words _ word hRead)

def getWithWork {n : ℕ} (store : Store n) (index : List Bool) : Option SignedWord × ℕ :=
  let slot := BinaryReferenceVector.readWithWork store.slots index
  match slot.1 with
  | none => (none,slot.2+4)
  | some pointer =>
      let object := BinaryPRGWordStoreHeapMachine.readWithWork store.heap.tape pointer
      (match object.1 with | some (.leaf word) => some word | _ => none,slot.2+object.2.work+4)

theorem getWithWork_state {n : ℕ} (store : Store n) (index : List Bool) : (getWithWork store index).1 = get store index := by
  unfold getWithWork get
  dsimp only
  cases hSlot : (BinaryReferenceVector.readWithWork store.slots index).1 with
  | none => simp only [Option.bind_none]
  | some pointer => simp only [Option.bind_some,BinaryPRGWordStoreHeapMachine.readWithWork_erasure,leafRead]

def readBound {n : ℕ} (store : Store n) (indexWidth : ℕ) : ℕ :=
  BinaryReferenceVector.readBound store.slots.length indexWidth+
    BinaryPRGWordStoreHeapMachine.readBound store.heap.tape.length (binaryWordWidth store.heap.tape.length)+8

theorem getWithWork_bound {n : ℕ} (store : Store n) (index : List Bool) :
    (getWithWork store index).2 ≤ readBound store index.length := by
  have hs := BinaryReferenceVector.readWithWork_bound store.slots index
  unfold getWithWork
  dsimp only
  split
  · unfold readBound
    omega
  · rename_i pointer hSlot
    obtain ⟨pointers,words,hLength,hSlots,hLinks⟩ := store.realized
    have hIndex : pointers[BinaryBigEndian.littleValue index]? = some pointer := by
      simpa only [hSlots,BinaryReferenceVector.read_encoded] using hSlot
    obtain ⟨word,hWord⟩ := hLinks.contains pointer (getElemOption_mem _ _ _ hIndex)
    have hObject := (BinaryPRGWordStoreHeapMachine.readContains_bounds hWord).2.1
    unfold readBound
    omega

end Blotto.BinaryWordObjectArray
