import Blotto.BinaryPRGWordStoreHeapMachine

/-! A measured Boolean tape store retains no logical tree as a data field.
The tree is a type index used by erased validity/refinement proofs. Every read
and selected persistent write runs the physical tape interpreter. Bounds use
the reached heap and its derived post-write reservation, rather than an
accepted access price or final-heap oracle. Full resource/controller adoption
and complete arithmetic/metadata/lifetime composition remain separate. -/

namespace Blotto.BinaryPRGHeapStoredTree
open BinaryRationalNormalization BinaryPRGWordStoreHeap
open BinaryPRGWordStoreHeapMachine
open BinaryPRGWordControllerWordStore (Tree)

structure Stored {depth : ℕ} (tree : Tree depth) where
  ruler : List Bool
  size : ruler.length = depth
  heap : Heap
  root : Pointer
  valid : Valid heap
  realizes : Realizes heap.tape root tree

def Stored.reindex {depth : ℕ} {first second : Tree depth} (h : first = second)
    (data : Stored first) : Stored second :=
  ⟨data.ruler,data.size,data.heap,data.root,data.valid,h ▸ data.realizes⟩

variable {depth : ℕ} {tree : Tree depth}

def prepareRulerWithWork (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    Stored (BinaryPRGWordControllerWordStore.build fallback ruler items).1 × Charge :=
  let executed := buildWithWork fallback ruler items empty
  (⟨ruler,rfl,executed.1.heap,executed.1.root,
    (by rw [buildWithWork_erasure]; exact (build_contract fallback ruler items empty empty_valid).1),
    (by rw [buildWithWork_erasure]; exact (build_contract fallback ruler items empty empty_valid).2.2.1)⟩,executed.2)

theorem prepareRulerWithWork_workBound (fallback : SignedWord)
    (ruler : List Bool) (items : List SignedWord) :
    (prepareRulerWithWork fallback ruler items).2.work ≤
      nodes ruler.length *
        (allocationBound (prepareRulerWithWork fallback ruler items).1.heap.tape.length + 8) := by
  have h := (buildWithWork_bounds fallback ruler items empty empty_valid
    (BinaryPRGWordStoreHeap.build fallback ruler items empty).heap.tape.length le_rfl).1
  unfold prepareRulerWithWork
  dsimp only
  rw [buildWithWork_erasure]
  exact h

theorem prepareRulerWithWork_allocatedBound (fallback : SignedWord)
    (ruler : List Bool) (items : List SignedWord) :
    (prepareRulerWithWork fallback ruler items).2.allocatedBits ≤
      nodes ruler.length *
        (allocationBound (prepareRulerWithWork fallback ruler items).1.heap.tape.length + 8) := by
  have h := (buildWithWork_bounds fallback ruler items empty empty_valid
    (BinaryPRGWordStoreHeap.build fallback ruler items empty).heap.tape.length le_rfl).2
  unfold prepareRulerWithWork
  dsimp only
  rw [buildWithWork_erasure]
  exact h

def prepareWithWork (fallback : SignedWord) (items : List SignedWord) :
    Stored (BinaryPRGWordControllerWordStore.prepare fallback items).tree × Charge :=
  let executed := BinaryPRGWordStoreHeapMachine.prepareWithWork fallback items
  (⟨executed.1.capBits,(by rw [prepareWithWork_erasure]; rfl),
    executed.1.heap,executed.1.root,
    (by rw [prepareWithWork_erasure]; exact prepare_valid fallback items),
    (by rw [prepareWithWork_erasure]; exact prepare_realizes fallback items)⟩,executed.2)

theorem prepareWithWork_bounds (fallback : SignedWord) (items : List SignedWord) :
    (prepareWithWork fallback items).1.heap.tape.length ≤ sourceHeapBound fallback items ∧
      (prepareWithWork fallback items).2.work ≤ preparationBound fallback items ∧
      (prepareWithWork fallback items).2.allocatedBits ≤ preparationBound fallback items := by
  have h := BinaryPRGWordStoreHeapMachine.prepareWithWork_bounds fallback items
  unfold prepareWithWork
  dsimp only
  rw [prepareWithWork_erasure]
  exact ⟨prepared_source_heap fallback items,h⟩

def readWithWork (data : Stored tree) (address : FixedBinaryWord depth) : SignedWord × Charge :=
  let executed := lookupWithWork data.heap.tape data.root data.ruler address.bits.reverse
  (executed.1.get (by
    rw [lookupWithWork_erasure, lookup_realizes data.realizes data.ruler address.bits.reverse data.size
      (by rw [List.length_reverse,address.size])]
    rfl), executed.2.add ⟨4 * address.bits.length + 2, 2 * address.bits.length⟩)

theorem readWithWork_value (data : Stored tree) (address : FixedBinaryWord depth) :
    (readWithWork data address).1 = BinaryPRGWordControllerWordStore.lookup tree address := by
  unfold readWithWork
  dsimp only
  simp only [lookupWithWork_erasure,
    lookup_realizes data.realizes data.ruler address.bits.reverse data.size
      (by rw [List.length_reverse,address.size])]
  rfl

def readBound (cells depth : ℕ) : ℕ := lookupBound cells depth + 4 * depth + 2

theorem readWithWork_bounds (data : Stored tree) (address : FixedBinaryWord depth) :
    (readWithWork data address).2.work ≤ readBound data.heap.tape.length depth ∧
      (readWithWork data address).2.allocatedBits ≤ lookupAllocation data.heap.tape.length depth + 2 * depth := by
  have h := lookupWithWork_bounds data.realizes data.ruler address.bits.reverse data.size
    (by rw [List.length_reverse,address.size])
  unfold readWithWork readBound Charge.add
  dsimp only
  rw [address.size]
  exact ⟨by omega,by omega⟩

theorem write_isSome (data : Stored tree) (address : FixedBinaryWord depth) (word : SignedWord) :
    (patchWithWork data.heap data.root data.ruler address.bits.reverse word).1.isSome := by
  obtain ⟨result,hResult,hValid,hExt,hRealizes⟩ := patch_contract tree data.heap data.root data.valid data.realizes
    data.ruler address.bits.reverse data.size (by rw [List.length_reverse,address.size]) word
  rw [patchWithWork_erasure,hResult]
  rfl

theorem write_result (data : Stored tree) (address : FixedBinaryWord depth) (word : SignedWord)
    (result : Pointer × Heap)
    (h : (patchWithWork data.heap data.root data.ruler address.bits.reverse word).1 = some result) :
    Valid result.2 ∧ Extends result.2 data.heap ∧
      Realizes result.2.tape result.1 (BinaryPRGWordControllerWordStore.write tree address word) := by
  obtain ⟨produced,hProduced,hValid,hExt,hRealizes⟩ := patch_contract tree data.heap data.root data.valid data.realizes
    data.ruler address.bits.reverse data.size (by rw [List.length_reverse,address.size]) word
  rw [patchWithWork_erasure,hProduced] at h
  cases h
  exact ⟨hValid,hExt,hRealizes⟩

def writeWithWork (data : Stored tree) (address : FixedBinaryWord depth) (word : SignedWord) :
    Stored (BinaryPRGWordControllerWordStore.write tree address word) × Charge :=
  let executed := patchWithWork data.heap data.root data.ruler address.bits.reverse word
  let result := executed.1.get (write_isSome data address word)
  let hResult : executed.1 = some result := (Option.some_get (write_isSome data address word)).symm
  let hContract := write_result data address word result hResult
  (⟨data.ruler,data.size,result.2,result.1,hContract.1,hContract.2.2⟩,executed.2)

theorem writeWithWork_extends (data : Stored tree) (address : FixedBinaryWord depth) (word : SignedWord) :
    Extends (writeWithWork data address word).1.heap data.heap := by
  unfold writeWithWork
  exact (write_result data address word _ (Option.some_get (write_isSome data address word)).symm).2.1

def writeHeapBound (data : Stored tree) (word : SignedWord) : ℕ :=
  heapBound (patchRawBound data.heap data.ruler word)

theorem writeWithWork_bounds (data : Stored tree) (address : FixedBinaryWord depth) (word : SignedWord) :
    (writeWithWork data address word).1.heap.tape.length ≤ writeHeapBound data word ∧
      (writeWithWork data address word).2.work ≤ patchBound (writeHeapBound data word) depth ∧
      (writeWithWork data address word).2.allocatedBits ≤ patchBound (writeHeapBound data word) depth := by
  obtain ⟨result,hResult,hHeap,hWork,hAllocation⟩ := patch_source_bounds tree data.heap data.root data.valid data.realizes
    data.ruler address.bits.reverse data.size (by rw [List.length_reverse,address.size]) word
  unfold writeWithWork writeHeapBound
  dsimp only
  simp only [hResult]
  exact ⟨hHeap,hWork,hAllocation⟩


theorem writeWithWork_result (data : Stored tree) (address : FixedBinaryWord depth) (word : SignedWord) :
    (patchWithWork data.heap data.root data.ruler address.bits.reverse word).1 =
      some ((writeWithWork data address word).1.root,(writeWithWork data address word).1.heap) := by
  unfold writeWithWork
  exact (Option.some_get (write_isSome data address word)).symm

def stepHeapBound (data : Stored tree) (word : SignedWord) (P : ℕ) : ℕ :=
  data.heap.tape.length + (depth + 1 + word.numerator.length + word.denominator.length) * (4 * P + 5)

theorem writeWithWork_controlled (data : Stored tree) (address : FixedBinaryWord depth) (word : SignedWord)
    (P : ℕ) (hP : 0 < P) (hRoom : stepHeapBound data word P < 2^P) :
    (writeWithWork data address word).1.heap.tape.length ≤ stepHeapBound data word P ∧
      (writeWithWork data address word).2.work ≤ patchBound (stepHeapBound data word P) depth ∧
      (writeWithWork data address word).2.allocatedBits ≤ patchBound (stepHeapBound data word P) depth := by
  let result := ((writeWithWork data address word).1.root,(writeWithWork data address word).1.heap)
  have hResult : patch data.heap data.root data.ruler address.bits.reverse word = some result := by
    rw [← patchWithWork_erasure]
    exact writeWithWork_result data address word
  have hSize := patch_size tree data.heap data.root data.valid data.realizes data.ruler address.bits.reverse
    data.size (by rw [List.length_reverse,address.size]) word P hP (by simpa only [data.size,stepHeapBound] using hRoom) result hResult
  have hSize' : result.2.tape.length ≤ stepHeapBound data word P := by
    simpa only [data.size,stepHeapBound] using hSize
  have hPrice := patchWithWork_bounds tree data.heap data.root data.valid data.realizes data.ruler address.bits.reverse
    data.size (by rw [List.length_reverse,address.size]) word result hResult (stepHeapBound data word P) hSize'
  exact ⟨hSize',hPrice⟩

theorem patchBound_mono {first second : ℕ} (h : first ≤ second) (depth : ℕ) :
    patchBound first depth ≤ patchBound second depth := by
  have hw := binaryWordWidth_mono h
  unfold patchBound BinaryPRGWordStoreHeapMachine.readBound skipBound allocationBound
  gcongr


theorem realizes_unique {depth : ℕ} {tape : List Bool} {pointer : Pointer} {first second : Tree depth}
    (hFirst : Realizes tape pointer first) (hSecond : Realizes tape pointer second) : first = second := by
  induction hFirst with
  | leaf word cell =>
      cases hSecond with
      | leaf other otherCell =>
          have he := Option.some.inj ((contains_read cell).symm.trans (contains_read otherCell))
          cases he
          rfl
  | branch cell left right ihLeft ihRight =>
      cases hSecond with
      | branch otherCell otherLeft otherRight =>
          have he := Option.some.inj ((contains_read cell).symm.trans (contains_read otherCell))
          cases he
          rw [ihLeft otherLeft,ihRight otherRight]

end Blotto.BinaryPRGHeapStoredTree
