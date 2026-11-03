import Blotto.BinaryPRGHeapResourceUpdateBudget

/-! A decreasing active-list reservation supplies the physical loop's step
budget. The pointer reservation is derived once from the incoming heap, input
count, address depth and native lattice width. -/

namespace Blotto.BinaryPRGHeapResourceReservation
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapResourceUpdateBudget (growth updateBound)

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,
  CanonicalWord (lookup capacity.tree address.word)}

def Reserved (D P H : ℕ) (state : Finished capacity n hCount) : Prop :=
  BinaryPRGHeapResourceInvariant.latticeInv D state ∧
    state.heap.tape.length + state.active.length *
      growth capacity.width (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) P ≤ H

def pairBound (D depth seedWidth seedCap C H : ℕ) : ℕ :=
  BinaryPRGWordControllerBooleanResourcePair.bound depth
      (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) +
    2 * BinaryPRGHeapStoredTree.readBound C depth +
    2 * BinaryPRGHeapStoredTree.readBound H depth +
    BinaryWordIndexCoinController.sampleBound
      (1 + 2 * binaryWordWidth D) seedWidth seedCap + 11

def stepBound (count D depth seedWidth seedCap C H : ℕ) : ℕ :=
  max (pairBound D depth seedWidth seedCap C H)
    (updateBound C H depth (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) count)

theorem reserved_room (D P H : ℕ) (state : Finished capacity n hCount)
    (hs : Reserved D P H state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    state.heap.tape.length + growth capacity.width
      (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) P ≤ H := by
  have hLength : 1 ≤ state.active.length := by rw [he]; simp
  have hm := Nat.mul_le_mul_right
    (growth capacity.width (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) P)
    hLength
  have hReserved := hs.2
  simpa only [one_mul] using (Nat.add_le_add_left hm state.heap.tape.length).trans hReserved

theorem select_reserved (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice
      (hC := hC) state first second tail he).outputs) (branch : Bool)
    (C H P : ℕ) (hCHeap : limits.heap.tape.length ≤ C) (hP : 0 < P)
    (hRoom : H < 2^P) (hs : Reserved D P H state) :
    Reserved D P H (BinaryPRGHeapResourceLoop.selectWithWork limits state
      first second tail he outputs hOutputs branch).1 ∧
      (BinaryPRGHeapResourceLoop.selectWithWork limits state first second tail he
        outputs hOutputs branch).2 ≤ updateBound C H capacity.width
          (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) n := by
  let selected := BinaryPRGHeapResourceLoop.selectWithWork limits state
    first second tail he outputs hOutputs branch
  have hUpdate := BinaryPRGHeapResourceUpdateBudget.selectWithWork_lattice_bound
    D hD hLattice hBox limits state hs.1 first second tail he outputs hOutputs branch
    C H P hCHeap hP (reserved_room D P H state hs first second tail he) hRoom
  have hProgress := BinaryPRGHeapResourceLoop.selectWithWork_progress
    limits state first second tail he outputs hOutputs branch
  change selected.1.active.length < state.active.length at hProgress
  have hLength : selected.1.active.length + 1 ≤ state.active.length := by omega
  have hm := Nat.mul_le_mul_right
    (growth capacity.width (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) P)
    hLength
  rw [Nat.add_mul,one_mul] at hm
  have hInvariant := BinaryPRGHeapResourceInvariant.selected_lattice
    D hLattice limits state first second tail he outputs hOutputs branch hs.1
  refine ⟨⟨hInvariant,?_⟩,hUpdate.2⟩
  have hHeap := hUpdate.1
  have hReserved := hs.2
  change selected.1.heap.tape.length + selected.1.active.length *
    growth capacity.width (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) P ≤ H
  change selected.1.heap.tape.length ≤ state.heap.tape.length +
    growth capacity.width (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) P at hHeap
  omega

theorem reachableStepBudget (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (C H P : ℕ) (hCHeap : limits.heap.tape.length ≤ C)
    (hP : 0 < P) (hRoom : H < 2^P) :
    BinaryPRGHeapResourceLoopBudget.ReachableStepBudget
      (capacity := capacity) (n := n) (hCount := hCount) seed limits hC
      (Reserved (capacity := capacity) (n := n) (hCount := hCount) D P H)
      (stepBound n D capacity.width seed.width seed.cap.value C H) := by
  refine ⟨?_,?_,?_⟩
  · intro state first second tail he pc hp hs
    have hHeap : state.heap.tape.length ≤ H := by have h := hs.2; omega
    exact (BinaryPRGHeapResourceCoinBudget.pair_coin_heapBound (hC := hC)
      D hD hLattice (fun j => (hBox j).2) seed limits state hs.1
      first second tail he pc hp C H hCHeap hHeap).trans (Nat.le_max_left _ _)
  · intro state first second tail he branch hs
    exact (select_reserved D hD hLattice hBox limits state first second tail he _
      (BinaryPRGHeapResourceLoop.pairWithWork_value
        (hC := hC) limits state first second tail he) branch C H P hCHeap hP hRoom hs).2.trans
      (Nat.le_max_right _ _)
  · intro state first second tail he branch hs
    exact (select_reserved D hD hLattice hBox limits state first second tail he _
      (BinaryPRGHeapResourceLoop.pairWithWork_value
        (hC := hC) limits state first second tail he) branch C H P hCHeap hP hRoom hs).1

def sourceSize (cells count depth W : ℕ) : ℕ :=
  cells + count * (2 * (depth + 1 + 2 * W))

def sourcePointerWidth (cells count depth W : ℕ) : ℕ := sourceSize cells count depth W + 10

def sourceHeapCap (cells count depth W : ℕ) : ℕ :=
  BinaryPRGWordStoreHeap.heapBound (sourceSize cells count depth W)

theorem source_room (cells count depth W : ℕ) :
    cells + count * growth depth W (sourcePointerWidth cells count depth W) ≤
      sourceHeapCap cells count depth W := by
  unfold growth sourcePointerWidth sourceHeapCap sourceSize BinaryPRGWordStoreHeap.heapBound
  rw [← Nat.mul_assoc]
  generalize count * (2 * (depth + 1 + 2 * W)) = payload
  nlinarith

theorem source_reserved (D : ℕ) (state : Finished capacity n hCount)
    (hs : BinaryPRGHeapResourceInvariant.latticeInv D state) :
    Reserved D
      (sourcePointerWidth state.heap.tape.length n capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D))
      (sourceHeapCap state.heap.tape.length n capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D)) state := by
  refine ⟨hs,?_⟩
  have hm := Nat.mul_le_mul_right
    (growth capacity.width (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D)
      (sourcePointerWidth state.heap.tape.length n capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D))) state.active_length_le
  exact (Nat.add_le_add_left hm _).trans (source_room _ _ _ _)

theorem runWithWork_source_bound (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity n hCount)
    (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).2 ≤
      n * (2 * stepBound n D capacity.width seed.width seed.cap.value
        limits.heap.tape.length
        (sourceHeapCap state.heap.tape.length n capacity.width
          (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D))) + 2 := by
  let P := sourcePointerWidth state.heap.tape.length n capacity.width
    (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D)
  let H := sourceHeapCap state.heap.tape.length n capacity.width
    (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D)
  have hP : 0 < P := by unfold P sourcePointerWidth; omega
  have hRoom : H < 2^P := BinaryPRGWordStoreHeap.quadratic_lt_capacity _
  have hBudget := reachableStepBudget (hC := hC) D hD hLattice hBox seed limits
    limits.heap.tape.length H P le_rfl hP hRoom
  exact BinaryPRGHeapResourceLoopBudget.runWithWork_inputCount_bound seed limits hC
    (Reserved D P H) _ hBudget state (source_reserved D state hs) pc hp

theorem runWithWork_source_reserved (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity n hCount)
    (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (result : Finished capacity n hCount)
    (hSome : (BinaryPRGHeapResourceLoop.runWithWork seed limits hC state pc hp).1.1 = some result) :
    Reserved D
      (sourcePointerWidth state.heap.tape.length n capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D))
      (sourceHeapCap state.heap.tape.length n capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D)) result := by
  let P := sourcePointerWidth state.heap.tape.length n capacity.width
    (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D)
  let H := sourceHeapCap state.heap.tape.length n capacity.width
    (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D)
  have hP : 0 < P := by unfold P sourcePointerWidth; omega
  have hRoom : H < 2^P := BinaryPRGWordStoreHeap.quadratic_lt_capacity _
  have hBudget := reachableStepBudget (hC := hC) D hD hLattice hBox seed limits
    limits.heap.tape.length H P le_rfl hP hRoom
  exact BinaryPRGHeapResourceLoopBudget.runWithWork_invariant seed limits hC
    (Reserved D P H) _ hBudget state (source_reserved D state hs) pc hp result hSome

end Blotto.BinaryPRGHeapResourceReservation
