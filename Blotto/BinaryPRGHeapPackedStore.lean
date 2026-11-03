import Blotto.BinaryPRGHeapStoredTree

/-! A recursive caller can retain a tape store with its logical tree only in
an existential proof. Consecutive writes therefore do not execute shadow tree
updates to pass a logical type index to the next recursive call. -/

namespace Blotto.BinaryPRGHeapPackedStore
open BinaryRationalNormalization BinaryPRGWordStoreHeap
open BinaryPRGWordStoreHeapMachine (Charge)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGWordControllerWordStore (Tree write)

structure Packed (depth : ℕ) where
  ruler : List Bool
  size : ruler.length = depth
  heap : Heap
  root : Pointer
  valid : Valid heap
  realized : ∃ tree : Tree depth, Realizes heap.tape root tree

noncomputable def Packed.reference {depth : ℕ} (data : Packed depth) : Tree depth := data.realized.choose

noncomputable def Packed.stored {depth : ℕ} (data : Packed depth) : Stored data.reference :=
  ⟨data.ruler,data.size,data.heap,data.root,data.valid,data.realized.choose_spec⟩

def pack {depth : ℕ} {tree : Tree depth} (data : Stored tree) : Packed depth :=
  ⟨data.ruler,data.size,data.heap,data.root,data.valid,⟨tree,data.realizes⟩⟩

def Packed.readWithWork {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) : SignedWord × Charge :=
  let executed := BinaryPRGWordStoreHeapMachine.lookupWithWork data.heap.tape data.root data.ruler address.bits.reverse
  (executed.1.get (by
    obtain ⟨tree,hTree⟩ := data.realized
    rw [BinaryPRGWordStoreHeapMachine.lookupWithWork_erasure,
      lookup_realizes hTree data.ruler address.bits.reverse data.size (by rw [List.length_reverse,address.size])]
    rfl),executed.2.add ⟨4 * address.bits.length + 2,2 * address.bits.length⟩)

theorem Packed.readWithWork_stored {depth : ℕ} (data : Packed depth) {tree : Tree depth}
    (h : Realizes data.heap.tape data.root tree) (address : FixedBinaryWord depth) :
    data.readWithWork address = BinaryPRGHeapStoredTree.readWithWork
      (⟨data.ruler,data.size,data.heap,data.root,data.valid,h⟩ : Stored tree) address := by
  rfl

theorem Packed.readWithWork_value {depth : ℕ} (data : Packed depth) {tree : Tree depth}
    (h : Realizes data.heap.tape data.root tree) (address : FixedBinaryWord depth) :
    (data.readWithWork address).1 = BinaryPRGWordControllerWordStore.lookup tree address := by
  rw [Packed.readWithWork_stored data h]
  exact BinaryPRGHeapStoredTree.readWithWork_value _ _

theorem Packed.readWithWork_bounds {depth : ℕ} (data : Packed depth)
    (address : FixedBinaryWord depth) :
    (data.readWithWork address).2.work ≤
      BinaryPRGHeapStoredTree.readBound data.heap.tape.length depth := by
  obtain ⟨tree,hTree⟩ := data.realized
  rw [Packed.readWithWork_stored data hTree]
  exact (BinaryPRGHeapStoredTree.readWithWork_bounds
    (⟨data.ruler,data.size,data.heap,data.root,data.valid,hTree⟩ : Stored tree) address).1

theorem Packed.write_isSome {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    (BinaryPRGWordStoreHeapMachine.patchWithWork data.heap data.root data.ruler address.bits.reverse word).1.isSome := by
  obtain ⟨tree,hTree⟩ := data.realized
  exact BinaryPRGHeapStoredTree.write_isSome (⟨data.ruler,data.size,data.heap,data.root,data.valid,hTree⟩ : Stored tree) address word

theorem Packed.write_result {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (result : Pointer × Heap)
    (h : (BinaryPRGWordStoreHeapMachine.patchWithWork data.heap data.root data.ruler address.bits.reverse word).1 = some result) :
    Valid result.2 ∧ ∃ tree : Tree depth,Realizes result.2.tape result.1 tree := by
  obtain ⟨tree,hTree⟩ := data.realized
  have hc := BinaryPRGHeapStoredTree.write_result (⟨data.ruler,data.size,data.heap,data.root,data.valid,hTree⟩ : Stored tree) address word result h
  exact ⟨hc.1,⟨_,hc.2.2⟩⟩

def Packed.writeWithWork {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    Packed depth × Charge :=
  let executed := BinaryPRGWordStoreHeapMachine.patchWithWork data.heap data.root data.ruler address.bits.reverse word
  let result := executed.1.get (data.write_isSome address word)
  let hResult : executed.1 = some result := (Option.some_get (data.write_isSome address word)).symm
  let h := data.write_result address word result hResult
  (⟨data.ruler,data.size,result.2,result.1,h.1,h.2⟩,executed.2)

theorem Packed.writeWithWork_stored {depth : ℕ} (data : Packed depth) {tree : Tree depth}
    (h : Realizes data.heap.tape data.root tree) (address : FixedBinaryWord depth) (word : SignedWord) :
    data.writeWithWork address word =
      let executed := BinaryPRGHeapStoredTree.writeWithWork
        (⟨data.ruler,data.size,data.heap,data.root,data.valid,h⟩ : Stored tree) address word
      (pack executed.1,executed.2) := by
  rfl

theorem Packed.writeWithWork_realizes {depth : ℕ} (data : Packed depth) {tree : Tree depth}
    (h : Realizes data.heap.tape data.root tree) (address : FixedBinaryWord depth) (word : SignedWord) :
    Realizes (data.writeWithWork address word).1.heap.tape (data.writeWithWork address word).1.root (write tree address word) := by
  rw [Packed.writeWithWork_stored data h]
  exact (BinaryPRGHeapStoredTree.writeWithWork
    (⟨data.ruler,data.size,data.heap,data.root,data.valid,h⟩ : Stored tree) address word).1.realizes

theorem Packed.writeWithWork_controlled {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (P : ℕ) (hP : 0 < P)
    (hRoom : data.heap.tape.length + (depth + 1 + word.numerator.length + word.denominator.length) * (4 * P + 5) < 2^P) :
    (data.writeWithWork address word).1.heap.tape.length ≤
      data.heap.tape.length + (depth + 1 + word.numerator.length + word.denominator.length) * (4 * P + 5) ∧
      (data.writeWithWork address word).2.work ≤ BinaryPRGWordStoreHeapMachine.patchBound
        (data.heap.tape.length + (depth + 1 + word.numerator.length + word.denominator.length) * (4 * P + 5)) depth ∧
      (data.writeWithWork address word).2.allocatedBits ≤ BinaryPRGWordStoreHeapMachine.patchBound
        (data.heap.tape.length + (depth + 1 + word.numerator.length + word.denominator.length) * (4 * P + 5)) depth := by
  obtain ⟨tree,hTree⟩ := data.realized
  rw [Packed.writeWithWork_stored data hTree]
  exact BinaryPRGHeapStoredTree.writeWithWork_controlled
    (⟨data.ruler,data.size,data.heap,data.root,data.valid,hTree⟩ : Stored tree) address word P hP hRoom

end Blotto.BinaryPRGHeapPackedStore
