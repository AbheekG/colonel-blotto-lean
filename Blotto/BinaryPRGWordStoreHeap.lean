import Blotto.BinaryPRGWordControllerWordStore
import Blotto.BinaryPRGWordControllerWordWalk
import Blotto.BinaryStoredCountdown
import Blotto.BinaryWordStoreLifetime

/-! A concrete finite Boolean tape heap. Child references are stored Boolean
absolute bit addresses, with their own self-delimited fields. The allocator
advances a retained Boolean carry counter while appending actual cell bits;
physical reads execute a Boolean countdown over the tape. Natural positions
occur only in refinement and size proofs. No heap-layout or access-price oracle
is supplied. This module interprets WordStore cells; arithmetic scratch storage
and complete caller/compiler/lifetime interpretation remain separate. -/
namespace Blotto.BinaryPRGWordStoreHeap
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore

abbrev Pointer := List Bool

inductive Cell where
  | leaf (word : SignedWord)
  | branch (left right : Pointer)

def field : List Bool → List Bool
  | [] => [false]
  | bit :: rest => true :: bit :: field rest

theorem field_length (bits : List Bool) : (field bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [field,List.length_cons,ih]; omega

def readField : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([],rest)
  | true :: bit :: rest => (readField rest).map (fun later => (bit :: later.1,later.2))
  | _ => none

theorem readField_field (bits suffix : List Bool) : readField (field bits ++ suffix) = some (bits,suffix) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [field,List.cons_append,readField,ih,Option.map_some]

def encode : Cell → List Bool
  | .leaf word => false :: word.negative :: (field word.numerator ++ field word.denominator)
  | .branch left right => true :: (field left ++ field right)

def decode : List Bool → Option Cell
  | false :: negative :: rest => do
      let first ← readField rest
      let second ← readField first.2
      pure (.leaf ⟨negative,first.1,second.1⟩)
  | true :: rest => do
      let first ← readField rest
      let second ← readField first.2
      pure (.branch first.1 second.1)
  | _ => none

theorem decode_encode (cell : Cell) (suffix : List Bool) : decode (encode cell ++ suffix) = some cell := by
  cases cell with
  | leaf word => simp [encode,decode,readField_field,List.append_assoc]
  | branch left right => simp [encode,decode,readField_field,List.append_assoc]

def skip (tape : List Bool) (pointer : Pointer) : List Bool :=
  if BinaryEuclideanGCD.nonzero pointer then
    match tape with
    | [] => []
    | _ :: rest => skip rest (BinaryStoredCountdown.predecessor pointer)
  else tape
termination_by tape.length

theorem skip_drop (tape : List Bool) (pointer : Pointer) : skip tape pointer = tape.drop (BinaryBigEndian.littleValue pointer) := by
  induction tape generalizing pointer with
  | nil => simp [skip,List.drop_nil]
  | cons bit rest ih =>
      unfold skip
      by_cases hn : BinaryEuclideanGCD.nonzero pointer = true
      · simp only [hn,ite_true,ih]
        have hp := BinaryStoredCountdown.predecessor_value pointer ((BinaryEuclideanGCD.nonzero_true_iff pointer).mp hn)
        rw [← hp,List.drop_succ_cons]
      · have hz : BinaryBigEndian.littleValue pointer = 0 := by
          have h := (BinaryEuclideanGCD.nonzero_true_iff pointer).not.mp hn
          omega
        simp only [Bool.eq_false_iff.mpr hn,Bool.false_eq_true,ite_false,hz,List.drop_zero]

def read (tape : List Bool) (pointer : Pointer) : Option Cell := decode (skip tape pointer)

structure Heap where
  tape : List Bool
  next : Pointer

def Valid (heap : Heap) : Prop := heap.next = BinaryCarryCounter.count heap.tape []

def empty : Heap := ⟨[],[]⟩

theorem empty_valid : Valid empty := rfl

def allocate (heap : Heap) (cell : Cell) : Pointer × Heap :=
  let bits := encode cell
  (heap.next,⟨heap.tape ++ bits,BinaryCarryCounter.count bits heap.next⟩)

theorem count_append {α : Type*} (first second : List α) (counter : List Bool) :
    BinaryCarryCounter.count (first ++ second) counter = BinaryCarryCounter.count second (BinaryCarryCounter.count first counter) := by
  induction first generalizing counter with
  | nil => rfl
  | cons item rest ih => simpa only [List.cons_append,BinaryCarryCounter.count] using ih (BinaryCarryCounter.increment counter)

theorem allocate_valid (heap : Heap) (cell : Cell) (h : Valid heap) : Valid (allocate heap cell).2 := by
  unfold Valid allocate
  dsimp only
  rw [h,count_append]

def Contains (tape : List Bool) (pointer : Pointer) (cell : Cell) : Prop :=
  ∃ beforeBits suffix, tape = beforeBits ++ encode cell ++ suffix ∧ pointer = BinaryCarryCounter.count beforeBits []

theorem contains_read {tape : List Bool} {pointer : Pointer} {cell : Cell} (h : Contains tape pointer cell) :
    read tape pointer = some cell := by
  obtain ⟨beforeBits,suffix,ht,hp⟩ := h
  unfold read
  rw [skip_drop,hp]
  change decode (tape.drop (BinaryCarryCounter.value (BinaryCarryCounter.count beforeBits []))) = _
  rw [BinaryCarryCounter.count_value,show BinaryCarryCounter.value [] = 0 from rfl,Nat.zero_add]
  simp only [ht,List.append_assoc,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append,decode_encode]

theorem allocate_contains (heap : Heap) (cell : Cell) (h : Valid heap) :
    Contains (allocate heap cell).2.tape (allocate heap cell).1 cell := by
  exact ⟨heap.tape,[],by simp only [allocate,List.append_nil],h⟩

def Extends (new old : Heap) : Prop := ∃ suffix,new.tape = old.tape ++ suffix

theorem extends_refl (heap : Heap) : Extends heap heap := ⟨[],(List.append_nil _).symm⟩

theorem extends_trans {first second third : Heap} (h1 : Extends first second) (h2 : Extends second third) : Extends first third := by
  obtain ⟨later,hLater⟩ := h1
  obtain ⟨earlier,hEarlier⟩ := h2
  exact ⟨earlier ++ later,by rw [hLater,hEarlier,List.append_assoc]⟩

theorem allocate_extends (heap : Heap) (cell : Cell) : Extends (allocate heap cell).2 heap := ⟨encode cell,rfl⟩

theorem contains_extends {new old : Heap} (he : Extends new old) {pointer : Pointer} {cell : Cell}
    (h : Contains old.tape pointer cell) : Contains new.tape pointer cell := by
  obtain ⟨later,hLater⟩ := he
  obtain ⟨beforeBits,suffix,ht,hp⟩ := h
  exact ⟨beforeBits,suffix ++ later,by rw [hLater,ht,List.append_assoc,List.append_assoc],hp⟩

inductive Realizes (tape : List Bool) : {depth : ℕ} → Pointer → Tree depth → Prop
  | leaf {pointer : Pointer} (word : SignedWord) (cell : Contains tape pointer (.leaf word)) : Realizes tape pointer (.leaf word)
  | branch {depth : ℕ} {pointer leftPointer rightPointer : Pointer} {left right : Tree depth}
      (cell : Contains tape pointer (.branch leftPointer rightPointer))
      (left_realizes : Realizes tape leftPointer left) (right_realizes : Realizes tape rightPointer right) :
      Realizes tape pointer (.branch left right)

theorem realizes_extends {new old : Heap} (he : Extends new old) {depth : ℕ} {pointer : Pointer} {tree : Tree depth}
    (h : Realizes old.tape pointer tree) : Realizes new.tape pointer tree := by
  induction h with
  | leaf word cell => exact .leaf word (contains_extends he cell)
  | branch cell left right ihl ihr => exact .branch (contains_extends he cell) ihl ihr

def lookup : List Bool → Pointer → List Bool → List Bool → Option SignedWord
  | tape,pointer,[],_ => match read tape pointer with
      | some (.leaf word) => some word
      | _ => none
  | tape,pointer,_ :: ruler,address => match read tape pointer with
      | some (.branch left right) =>
          if address.headD false then lookup tape right ruler address.tail else lookup tape left ruler address.tail
      | _ => none

theorem lookup_realizes {depth : ℕ} {tape : List Bool} {pointer : Pointer} {tree : Tree depth}
    (h : Realizes tape pointer tree) (ruler address : List Bool) (hr : ruler.length = depth) (ha : address.length = depth) :
    lookup tape pointer ruler address = some (scan tree address) := by
  induction h generalizing ruler address with
  | leaf word cell =>
      have he : ruler = [] := List.length_eq_zero_iff.mp hr
      subst ruler
      simp only [lookup,contains_read cell,scan]
  | branch cell hl hrTree ihl ihr =>
      cases ruler with
      | nil => simp at hr
      | cons ignored ruler =>
        cases address with
        | nil => simp at ha
        | cons bit address =>
          cases bit
          · simpa only [lookup,contains_read cell,List.headD_cons,List.tail_cons,scan,Bool.false_eq_true,ite_false] using
              ihl ruler address (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hr)
                (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using ha)
          · simpa only [lookup,contains_read cell,List.headD_cons,List.tail_cons,scan,ite_true] using
              ihr ruler address (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hr)
                (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using ha)

structure Built where
  root : Pointer
  heap : Heap
  remaining : List SignedWord

def build (fallback : SignedWord) : List Bool → List SignedWord → Heap → Built
  | [],[],heap =>
      let allocated := allocate heap (.leaf fallback)
      ⟨allocated.1,allocated.2,[]⟩
  | [],word :: rest,heap =>
      let allocated := allocate heap (.leaf word)
      ⟨allocated.1,allocated.2,rest⟩
  | _ :: ruler,items,heap =>
      let first := build fallback ruler items heap
      let second := build fallback ruler first.remaining first.heap
      let allocated := allocate second.heap (.branch first.root second.root)
      ⟨allocated.1,allocated.2,second.remaining⟩

theorem build_contract (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap)
    (hHeap : Valid heap) :
    Valid (build fallback ruler items heap).heap ∧ Extends (build fallback ruler items heap).heap heap ∧
      Realizes (build fallback ruler items heap).heap.tape (build fallback ruler items heap).root
        (BinaryPRGWordControllerWordStore.build fallback ruler items).1 ∧
      (build fallback ruler items heap).remaining = (BinaryPRGWordControllerWordStore.build fallback ruler items).2 := by
  induction ruler generalizing items heap with
  | nil =>
      cases items with
      | nil => exact ⟨allocate_valid _ _ hHeap,allocate_extends _ _,.leaf _ (allocate_contains _ _ hHeap),rfl⟩
      | cons word rest => exact ⟨allocate_valid _ _ hHeap,allocate_extends _ _,.leaf _ (allocate_contains _ _ hHeap),rfl⟩
  | cons bit ruler ih =>
      let first := build fallback ruler items heap
      let second := build fallback ruler first.remaining first.heap
      let allocated := allocate second.heap (.branch first.root second.root)
      obtain ⟨hFirst,hFirstExt,hFirstTree,hFirstRest⟩ := ih items heap hHeap
      change Valid first.heap at hFirst
      change Extends first.heap heap at hFirstExt
      change Realizes first.heap.tape first.root _ at hFirstTree
      change first.remaining = _ at hFirstRest
      obtain ⟨hSecond,hSecondExt,hSecondTree,hSecondRest⟩ := ih first.remaining first.heap hFirst
      change Valid second.heap at hSecond
      change Extends second.heap first.heap at hSecondExt
      change Realizes second.heap.tape second.root _ at hSecondTree
      change second.remaining = _ at hSecondRest
      have hTreeEq := congrArg (fun words => (BinaryPRGWordControllerWordStore.build fallback ruler words).1) hFirstRest
      have hRightTree : Realizes second.heap.tape second.root
          (BinaryPRGWordControllerWordStore.build fallback ruler (BinaryPRGWordControllerWordStore.build fallback ruler items).2).1 :=
        hTreeEq ▸ hSecondTree
      have hRightRest := hSecondRest.trans (congrArg (fun words => (BinaryPRGWordControllerWordStore.build fallback ruler words).2) hFirstRest)
      change Valid allocated.2 ∧ Extends allocated.2 heap ∧ Realizes allocated.2.tape allocated.1 _ ∧ second.remaining = _
      refine ⟨allocate_valid _ _ hSecond,extends_trans (extends_trans (allocate_extends _ _) hSecondExt) hFirstExt,?_,hRightRest⟩
      exact .branch (allocate_contains _ _ hSecond)
        (realizes_extends (extends_trans (allocate_extends _ _) hSecondExt) hFirstTree)
        (realizes_extends (allocate_extends _ _) hRightTree)

structure Store where
  capBits : List Bool
  heap : Heap
  root : Pointer

def Store.width (store : Store) : ℕ := store.capBits.length

def Store.cap (store : Store) : FixedBinaryWord store.width := ⟨store.capBits,rfl⟩

def prepare (fallback : SignedWord) (items : List SignedWord) : Store :=
  let ruler := BinaryCarryCounter.count items []
  let stored := build fallback ruler items empty
  ⟨ruler,stored.heap,stored.root⟩

def lookupStore (store : Store) (address : FixedBinaryWord store.width) : Option SignedWord :=
  lookup store.heap.tape store.root store.cap.bits address.bits.reverse

def readStore (store : Store) (address : FixedBinaryWord store.width) : Option SignedWord :=
  if BinaryIndexWord.lt address store.cap then lookupStore store address else none

theorem prepare_cap (fallback : SignedWord) (items : List SignedWord) :
    (prepare fallback items).cap.value = items.length := by
  change BinaryCarryCounter.value (BinaryCarryCounter.count items []) = _
  rw [BinaryCarryCounter.count_value,show BinaryCarryCounter.value [] = 0 from rfl,Nat.zero_add]

theorem prepare_valid (fallback : SignedWord) (items : List SignedWord) : Valid (prepare fallback items).heap :=
  (build_contract fallback (BinaryCarryCounter.count items []) items empty empty_valid).1

theorem prepare_realizes (fallback : SignedWord) (items : List SignedWord) :
    Realizes (prepare fallback items).heap.tape (prepare fallback items).root
      (BinaryPRGWordControllerWordStore.prepare fallback items).tree :=
  (build_contract fallback (BinaryCarryCounter.count items []) items empty empty_valid).2.2.1

theorem prepare_lookup (fallback : SignedWord) (items : List SignedWord)
    (address : FixedBinaryWord (prepare fallback items).width) :
    lookupStore (prepare fallback items) address = some (items.getD address.value fallback) := by
  have h := lookup_realizes (prepare_realizes fallback items) (prepare fallback items).cap.bits address.bits.reverse
    (prepare fallback items).cap.size (by rw [List.length_reverse,address.size]; rfl)
  exact h.trans (congrArg some (BinaryPRGWordControllerWordStore.prepare_lookup fallback items address))

theorem prepare_read (fallback : SignedWord) (items : List SignedWord)
    (address : FixedBinaryWord (prepare fallback items).width) :
    readStore (prepare fallback items) address = if address.value < items.length then some (items.getD address.value fallback) else none := by
  unfold readStore
  rw [prepare_lookup]
  have hGuard := BinaryIndexWord.lt_value address (prepare fallback items).cap
  rw [prepare_cap] at hGuard
  by_cases h : address.value < items.length
  · simp only [hGuard.mpr h,h,ite_true]
  · have hn := Bool.eq_false_iff.mpr (fun he => h (hGuard.mp he))
    simp only [hn,h,Bool.false_eq_true,ite_false]

def patch : Heap → Pointer → List Bool → List Bool → SignedWord → Option (Pointer × Heap)
  | heap,pointer,[],_,word => match read heap.tape pointer with
      | some (.leaf _) => some (allocate heap (.leaf word))
      | _ => none
  | heap,pointer,_ :: ruler,address,word => match read heap.tape pointer with
      | some (.branch left right) =>
          if address.headD false then do
            let changed ← patch heap right ruler address.tail word
            pure (allocate changed.2 (.branch left changed.1))
          else do
            let changed ← patch heap left ruler address.tail word
            pure (allocate changed.2 (.branch changed.1 right))
      | _ => none

theorem patch_contract {depth : ℕ} (tree : Tree depth) (heap : Heap) (pointer : Pointer)
    (hHeap : Valid heap) (hTree : Realizes heap.tape pointer tree)
    (ruler address : List Bool) (hr : ruler.length = depth) (ha : address.length = depth) (word : SignedWord) :
    ∃ changed : Pointer × Heap,patch heap pointer ruler address word = some changed ∧ Valid changed.2 ∧
      Extends changed.2 heap ∧ Realizes changed.2.tape changed.1 (writeScan tree address word) := by
  induction tree generalizing heap pointer ruler address with
  | leaf old =>
      have he : ruler = [] := List.length_eq_zero_iff.mp hr
      subst ruler
      cases hTree with
      | leaf old cell =>
          refine ⟨allocate heap (.leaf word),?_,allocate_valid _ _ hHeap,allocate_extends _ _,.leaf word (allocate_contains _ _ hHeap)⟩
          simp only [patch,contains_read cell]
  | @branch depth left right ihl ihr =>
      cases ruler with
      | nil => simp at hr
      | cons ignored ruler =>
        cases address with
        | nil => simp at ha
        | cons bit address =>
          have hr' : ruler.length = depth := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hr
          have ha' : address.length = depth := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using ha
          cases hTree with
          | @branch _ _ leftPointer rightPointer _ _ cell leftTree rightTree =>
            cases bit
            · obtain ⟨changed,hChanged,hValid,hExt,hRealizes⟩ := ihl heap leftPointer hHeap leftTree ruler address hr' ha'
              refine ⟨allocate changed.2 (.branch changed.1 rightPointer),?_,allocate_valid _ _ hValid,
                extends_trans (allocate_extends _ _) hExt,?_⟩
              · simp only [patch,contains_read cell,List.headD_cons,List.tail_cons,Bool.false_eq_true,ite_false,hChanged]
                rfl
              · exact .branch (allocate_contains _ _ hValid)
                  (realizes_extends (allocate_extends _ _) hRealizes)
                  (realizes_extends (extends_trans (allocate_extends _ _) hExt) rightTree)
            · obtain ⟨changed,hChanged,hValid,hExt,hRealizes⟩ := ihr heap rightPointer hHeap rightTree ruler address hr' ha'
              refine ⟨allocate changed.2 (.branch leftPointer changed.1),?_,allocate_valid _ _ hValid,
                extends_trans (allocate_extends _ _) hExt,?_⟩
              · simp only [patch,contains_read cell,List.headD_cons,List.tail_cons,ite_true,hChanged]
                rfl
              · exact .branch (allocate_contains _ _ hValid)
                  (realizes_extends (extends_trans (allocate_extends _ _) hExt) leftTree)
                  (realizes_extends (allocate_extends _ _) hRealizes)

def writeStore (store : Store) (address : FixedBinaryWord store.width) (word : SignedWord) : Option Store :=
  (patch store.heap store.root store.cap.bits address.bits.reverse word).map
    (fun changed => ⟨store.capBits,changed.2,changed.1⟩)

theorem prepared_write (fallback : SignedWord) (items : List SignedWord)
    (address : FixedBinaryWord (prepare fallback items).width) (word : SignedWord) :
    ∃ result : Store,writeStore (prepare fallback items) address word = some result ∧ Valid result.heap ∧
      result.width = (prepare fallback items).width ∧ HEq result.cap (prepare fallback items).cap ∧
      Realizes result.heap.tape result.root (BinaryPRGWordControllerWordStore.write
        (BinaryPRGWordControllerWordStore.prepare fallback items).tree address word) := by
  obtain ⟨changed,hChanged,hValid,hExt,hTree⟩ := patch_contract
    (BinaryPRGWordControllerWordStore.prepare fallback items).tree (prepare fallback items).heap (prepare fallback items).root
    (prepare_valid fallback items) (prepare_realizes fallback items) (prepare fallback items).cap.bits address.bits.reverse
    (prepare fallback items).cap.size (by rw [List.length_reverse,address.size]; rfl) word
  refine ⟨⟨(prepare fallback items).capBits,changed.2,changed.1⟩,?_,hValid,rfl,HEq.rfl,hTree⟩
  simp only [writeStore,hChanged,Option.map_some]

theorem next_width (heap : Heap) (h : Valid heap) : heap.next.length ≤ binaryWordWidth heap.tape.length := by
  rw [h]
  exact BinarySeedLookupTree.prepare_width_bound heap.tape

theorem contains_pointer_width {tape : List Bool} {pointer : Pointer} {cell : Cell} (h : Contains tape pointer cell) :
    pointer.length ≤ binaryWordWidth tape.length := by
  obtain ⟨beforeBits,suffix,ht,hp⟩ := h
  rw [hp]
  have hw := BinarySeedLookupTree.prepare_width_bound beforeBits
  apply hw.trans
  apply binaryWordWidth_mono
  simp only [ht,List.length_append]
  omega

theorem realizes_pointer_width {depth : ℕ} {tape : List Bool} {pointer : Pointer} {tree : Tree depth}
    (h : Realizes tape pointer tree) : pointer.length ≤ binaryWordWidth tape.length := by
  cases h with
  | leaf word cell => exact contains_pointer_width cell
  | branch cell left right => exact contains_pointer_width cell

def rawSize (fallback : SignedWord) : List Bool → List SignedWord → ℕ
  | [],[] => 1 + fallback.numerator.length + fallback.denominator.length
  | [],word :: _ => 1 + word.numerator.length + word.denominator.length
  | _ :: ruler,items => 1 + rawSize fallback ruler items +
      rawSize fallback ruler (BinaryPRGWordControllerWordStore.build fallback ruler items).2

theorem rawSize_pos (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) : 0 < rawSize fallback ruler items := by
  cases ruler with
  | nil => cases items <;> simp [rawSize]
  | cons bit ruler => simp only [rawSize]; omega

theorem encode_leaf_length (word : SignedWord) :
    (encode (.leaf word)).length = 2 * (word.numerator.length + word.denominator.length) + 4 := by
  simp only [encode,List.length_cons,List.length_append,field_length]
  omega

theorem encode_branch_length (left right : Pointer) :
    (encode (.branch left right)).length = 2 * (left.length + right.length) + 3 := by
  simp only [encode,List.length_cons,List.length_append,field_length]
  omega

theorem build_size (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) (heap : Heap)
    (hHeap : Valid heap) (P : ℕ) (hP : 0 < P)
    (hRoom : heap.tape.length + rawSize fallback ruler items * (4 * P + 5) < 2^P) :
    (build fallback ruler items heap).heap.tape.length ≤ heap.tape.length + rawSize fallback ruler items * (4 * P + 5) := by
  induction ruler generalizing items heap with
  | nil =>
      cases items with
      | nil =>
          change (heap.tape ++ encode (.leaf fallback)).length ≤ _
          rw [List.length_append,encode_leaf_length]
          simp only [rawSize]
          nlinarith
      | cons word rest =>
          change (heap.tape ++ encode (.leaf word)).length ≤ _
          rw [List.length_append,encode_leaf_length]
          simp only [rawSize]
          nlinarith
  | cons bit ruler ih =>
      let first := build fallback ruler items heap
      let second := build fallback ruler first.remaining first.heap
      obtain ⟨hFirst,hFirstExt,hFirstTree,hFirstRest⟩ := build_contract fallback ruler items heap hHeap
      change Valid first.heap at hFirst
      change first.remaining = _ at hFirstRest
      have hFirstRoom : heap.tape.length + rawSize fallback ruler items * (4 * P + 5) < 2^P := by
        simp only [rawSize] at hRoom
        nlinarith
      have hFirstSize := ih items heap hHeap hFirstRoom
      change first.heap.tape.length ≤ _ at hFirstSize
      have hRightRaw := congrArg (rawSize fallback ruler) hFirstRest
      have hSecondRoom : first.heap.tape.length + rawSize fallback ruler first.remaining * (4 * P + 5) < 2^P := by
        rw [hRightRaw]
        simp only [rawSize] at hRoom
        nlinarith
      have hSecondSize := ih first.remaining first.heap hFirst hSecondRoom
      change second.heap.tape.length ≤ _ at hSecondSize
      obtain ⟨hSecond,hSecondExt,hSecondTree,hSecondRest⟩ := build_contract fallback ruler first.remaining first.heap hFirst
      change Extends second.heap first.heap at hSecondExt
      change Realizes first.heap.tape first.root _ at hFirstTree
      change Realizes second.heap.tape second.root _ at hSecondTree
      have hTapeRoom : second.heap.tape.length < 2^P := by omega
      have hPointerBound := binaryWordWidth_le_of_lt_pow hP hTapeRoom
      have hLeft := (realizes_pointer_width (realizes_extends hSecondExt hFirstTree)).trans hPointerBound
      have hRight := (realizes_pointer_width hSecondTree).trans hPointerBound
      change (second.heap.tape ++ encode (.branch first.root second.root)).length ≤ _
      rw [List.length_append,encode_branch_length]
      simp only [rawSize]
      rw [hRightRaw] at hSecondSize
      nlinarith

theorem quadratic_lt_capacity (N : ℕ) : 5 * (N + 10)^2 < 2^(N + 10) := by
  induction N with
  | zero => decide
  | succ N ih =>
      rw [show N + 1 + 10 = N + 10 + 1 by omega,pow_succ]
      have hs : 5 * (N + 10 + 1)^2 ≤ 2 * (5 * (N + 10)^2) := by ring_nf; omega
      exact hs.trans_lt (by omega)

def heapBound (N : ℕ) : ℕ := 5 * (N + 10)^2

theorem prepared_heap_bound (fallback : SignedWord) (items : List SignedWord) :
    (prepare fallback items).heap.tape.length ≤ heapBound (rawSize fallback (BinaryCarryCounter.count items []) items) := by
  let N := rawSize fallback (BinaryCarryCounter.count items []) items
  have hProduct : N * (4 * (N + 10) + 5) ≤ heapBound N := by unfold heapBound; nlinarith
  have hRoom : empty.tape.length + N * (4 * (N + 10) + 5) < 2^(N + 10) := by
    simpa only [empty,List.length_nil,Nat.zero_add] using hProduct.trans_lt (quadratic_lt_capacity N)
  have h := build_size fallback (BinaryCarryCounter.count items []) items empty empty_valid (N + 10) (by omega) hRoom
  simp only [empty,List.length_nil,Nat.zero_add] at h
  exact h.trans hProduct

theorem prepared_pointer_bound (fallback : SignedWord) (items : List SignedWord) :
    (prepare fallback items).root.length ≤
      binaryWordWidth (heapBound (rawSize fallback (BinaryCarryCounter.count items []) items)) :=
  (realizes_pointer_width (prepare_realizes fallback items)).trans (binaryWordWidth_mono (prepared_heap_bound fallback items))

def rawTreeSize : {depth : ℕ} → Tree depth → ℕ
  | _,.leaf word => BinaryRationalExpression.payloadWords word
  | _,.branch left right => 1 + rawTreeSize left + rawTreeSize right

theorem rawSize_build (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    rawSize fallback ruler items = rawTreeSize (BinaryPRGWordControllerWordStore.build fallback ruler items).1 := by
  induction ruler generalizing items with
  | nil => cases items <;> rfl
  | cons bit ruler ih => simp only [rawSize,BinaryPRGWordControllerWordStore.build,rawTreeSize,ih]

theorem rawTreeSize_bound {depth : ℕ} (tree : Tree depth) :
    rawTreeSize tree + 1 ≤ 2^depth * (BinaryPRGWordControllerWordStore.maxPayload tree + 1) := by
  induction tree with
  | leaf word => simp only [rawTreeSize,BinaryPRGWordControllerWordStore.maxPayload,pow_zero,Nat.one_mul]; rfl
  | @branch depth left right ihl ihr =>
      have hl := ihl.trans (Nat.mul_le_mul_left (2^depth) (Nat.add_le_add_right (Nat.le_max_left (BinaryPRGWordControllerWordStore.maxPayload left) (BinaryPRGWordControllerWordStore.maxPayload right)) 1))
      have hr := ihr.trans (Nat.mul_le_mul_left (2^depth) (Nat.add_le_add_right (Nat.le_max_right (BinaryPRGWordControllerWordStore.maxPayload left) (BinaryPRGWordControllerWordStore.maxPayload right)) 1))
      simp only [rawTreeSize,BinaryPRGWordControllerWordStore.maxPayload,pow_succ]
      nlinarith

theorem prepare_rawSize_bound (fallback : SignedWord) (items : List SignedWord) (W : ℕ)
    (hFallback : BinaryRationalExpression.payloadWords fallback ≤ W)
    (hItems : ∀ word ∈ items,BinaryRationalExpression.payloadWords word ≤ W) :
    rawSize fallback (BinaryCarryCounter.count items []) items ≤ (2 * items.length + 1) * (W + 1) := by
  let ruler := BinaryCarryCounter.count items []
  have hm := BinaryPRGWordControllerWordStore.build_maxPayload_bound fallback ruler items W
    (BinaryPRGWordControllerWordStore.getD_payload_bound fallback items W hFallback hItems)
  have ht := rawTreeSize_bound (BinaryPRGWordControllerWordStore.build fallback ruler items).1
  have hc := BinaryPRGWordControllerWordStore.prepare_capacity_bound fallback items
  have hb := ht.trans (Nat.mul_le_mul hc (Nat.add_le_add_right hm 1))
  rw [← rawSize_build] at hb
  change rawSize fallback ruler items ≤ _
  exact (show rawSize fallback ruler items ≤ rawSize fallback ruler items + 1 by omega).trans hb

def inputPayload (fallback : SignedWord) : List SignedWord → ℕ
  | [] => BinaryRationalExpression.payloadWords fallback
  | word :: rest => max (BinaryRationalExpression.payloadWords word) (inputPayload fallback rest)

theorem inputPayload_fallback (fallback : SignedWord) (items : List SignedWord) :
    BinaryRationalExpression.payloadWords fallback ≤ inputPayload fallback items := by
  induction items with
  | nil => rfl
  | cons word rest ih => exact ih.trans (Nat.le_max_right _ _)

theorem inputPayload_member (fallback : SignedWord) (items : List SignedWord) (word : SignedWord) (h : word ∈ items) :
    BinaryRationalExpression.payloadWords word ≤ inputPayload fallback items := by
  induction items with
  | nil => cases h
  | cons first rest ih =>
      rcases List.mem_cons.mp h with he | ht
      · subst word
        exact Nat.le_max_left _ _
      · exact (ih ht).trans (Nat.le_max_right _ _)

def sourceRawBound (fallback : SignedWord) (items : List SignedWord) : ℕ :=
  (2 * items.length + 1) * (inputPayload fallback items + 1)

theorem prepared_raw_bound (fallback : SignedWord) (items : List SignedWord) :
    rawSize fallback (BinaryCarryCounter.count items []) items ≤ sourceRawBound fallback items :=
  prepare_rawSize_bound fallback items (inputPayload fallback items) (inputPayload_fallback _ _) (inputPayload_member _ _)

def sourceHeapBound (fallback : SignedWord) (items : List SignedWord) : ℕ := heapBound (sourceRawBound fallback items)

theorem heapBound_mono {first second : ℕ} (h : first ≤ second) : heapBound first ≤ heapBound second := by
  unfold heapBound
  gcongr

theorem prepared_source_heap (fallback : SignedWord) (items : List SignedWord) :
    (prepare fallback items).heap.tape.length ≤ sourceHeapBound fallback items :=
  (prepared_heap_bound fallback items).trans (heapBound_mono (prepared_raw_bound fallback items))

theorem prepared_source_pointer (fallback : SignedWord) (items : List SignedWord) :
    (prepare fallback items).root.length ≤ binaryWordWidth (sourceHeapBound fallback items) :=
  (prepared_pointer_bound fallback items).trans (binaryWordWidth_mono (heapBound_mono (prepared_raw_bound fallback items)))

def snapshot (store : Store) : List Bool :=
  field store.capBits ++ field store.root ++ field store.heap.next ++ field store.heap.tape

def restore (bits : List Bool) : Option (Store × List Bool) := do
  let cap ← readField bits
  let root ← readField cap.2
  let counter ← readField root.2
  let tape ← readField counter.2
  pure (⟨cap.1,⟨tape.1,counter.1⟩,root.1⟩,tape.2)

theorem restore_snapshot (store : Store) (suffix : List Bool) : restore (snapshot store ++ suffix) = some (store,suffix) := by
  cases store with
  | mk cap heap root =>
    cases heap
    simp [snapshot,restore,List.append_assoc,readField_field]

theorem snapshot_length (store : Store) :
    (snapshot store).length = 2 * (store.capBits.length + store.root.length + store.heap.next.length + store.heap.tape.length) + 4 := by
  simp only [snapshot,List.length_append,field_length]
  omega

theorem prepared_snapshot_bound (fallback : SignedWord) (items : List SignedWord) :
    (snapshot (prepare fallback items)).length ≤
      2 * (binaryWordWidth items.length + 2 * binaryWordWidth (sourceHeapBound fallback items) + sourceHeapBound fallback items) + 4 := by
  have hd := BinaryPRGWordControllerWordStore.prepare_width_bound fallback items
  have ht := prepared_source_heap fallback items
  have hr := prepared_source_pointer fallback items
  have hc := (next_width (prepare fallback items).heap (prepare_valid fallback items)).trans (binaryWordWidth_mono ht)
  rw [snapshot_length]
  change (BinaryCarryCounter.count items []).length ≤ binaryWordWidth items.length at hd
  change 2 * ((BinaryCarryCounter.count items []).length + _ + _ + _) + 4 ≤ _
  omega

theorem patch_size {depth : ℕ} (tree : Tree depth) (heap : Heap) (pointer : Pointer)
    (hHeap : Valid heap) (hTree : Realizes heap.tape pointer tree)
    (ruler address : List Bool) (hr : ruler.length = depth) (ha : address.length = depth) (word : SignedWord)
    (P : ℕ) (hP : 0 < P)
    (hRoom : heap.tape.length + (ruler.length + 1 + word.numerator.length + word.denominator.length) * (4 * P + 5) < 2^P)
    (changed : Pointer × Heap) (hChanged : patch heap pointer ruler address word = some changed) :
    changed.2.tape.length ≤ heap.tape.length + (ruler.length + 1 + word.numerator.length + word.denominator.length) * (4 * P + 5) := by
  induction tree generalizing heap pointer ruler address changed with
  | leaf old =>
      have he : ruler = [] := List.length_eq_zero_iff.mp hr
      subst ruler
      cases hTree with
      | leaf old cell =>
        simp only [patch,contains_read cell] at hChanged
        cases hChanged
        simp only [allocate,List.length_append,encode_leaf_length,List.length_nil]
        nlinarith
  | @branch depth left right ihl ihr =>
      cases ruler with
      | nil => simp at hr
      | cons ignored ruler =>
        cases address with
        | nil => simp at ha
        | cons bit address =>
          have hr' : ruler.length = depth := Nat.succ.inj hr
          have ha' : address.length = depth := Nat.succ.inj ha
          cases hTree with
          | @branch _ _ leftPointer rightPointer _ _ cell leftTree rightTree =>
            have hChildRoom : heap.tape.length + (ruler.length + 1 + word.numerator.length + word.denominator.length) * (4 * P + 5) < 2^P := by
              simp only [List.length_cons] at hRoom
              nlinarith
            cases bit
            · obtain ⟨child,hChild,hValid,hExt,hRealizes⟩ := patch_contract left heap leftPointer hHeap leftTree ruler address hr' ha' word
              have hSize := ihl heap leftPointer hHeap leftTree ruler address hr' ha' hChildRoom child hChild
              have hTapeRoom : child.2.tape.length < 2^P := hSize.trans_lt hChildRoom
              have hPointer := binaryWordWidth_le_of_lt_pow hP hTapeRoom
              have hpLeft := (realizes_pointer_width hRealizes).trans hPointer
              have hpRight := (realizes_pointer_width (realizes_extends hExt rightTree)).trans hPointer
              simp only [patch,contains_read cell,List.headD_cons,List.tail_cons,Bool.false_eq_true,ite_false,hChild] at hChanged
              cases hChanged
              simp only [allocate,List.length_append,encode_branch_length,List.length_cons]
              nlinarith
            · obtain ⟨child,hChild,hValid,hExt,hRealizes⟩ := patch_contract right heap rightPointer hHeap rightTree ruler address hr' ha' word
              have hSize := ihr heap rightPointer hHeap rightTree ruler address hr' ha' hChildRoom child hChild
              have hTapeRoom : child.2.tape.length < 2^P := hSize.trans_lt hChildRoom
              have hPointer := binaryWordWidth_le_of_lt_pow hP hTapeRoom
              have hpLeft := (realizes_pointer_width (realizes_extends hExt leftTree)).trans hPointer
              have hpRight := (realizes_pointer_width hRealizes).trans hPointer
              simp only [patch,contains_read cell,List.headD_cons,List.tail_cons,ite_true,hChild] at hChanged
              cases hChanged
              simp only [allocate,List.length_append,encode_branch_length,List.length_cons]
              nlinarith

def patchRawBound (heap : Heap) (ruler : List Bool) (word : SignedWord) : ℕ :=
  heap.tape.length + ruler.length + 1 + word.numerator.length + word.denominator.length

theorem patch_heap_bound {depth : ℕ} (tree : Tree depth) (heap : Heap) (pointer : Pointer)
    (hHeap : Valid heap) (hTree : Realizes heap.tape pointer tree)
    (ruler address : List Bool) (hr : ruler.length = depth) (ha : address.length = depth) (word : SignedWord)
    (changed : Pointer × Heap) (hChanged : patch heap pointer ruler address word = some changed) :
    changed.2.tape.length ≤ heapBound (patchRawBound heap ruler word) := by
  let N := patchRawBound heap ruler word
  have hProduct : heap.tape.length + (ruler.length + 1 + word.numerator.length + word.denominator.length) * (4 * (N + 10) + 5) ≤ heapBound N := by
    unfold heapBound
    have hN : N = heap.tape.length + ruler.length + 1 + word.numerator.length + word.denominator.length := rfl
    nlinarith
  have hRoom := hProduct.trans_lt (quadratic_lt_capacity N)
  exact (patch_size tree heap pointer hHeap hTree ruler address hr ha word (N + 10) (by omega) hRoom changed hChanged).trans hProduct

end Blotto.BinaryPRGWordStoreHeap
