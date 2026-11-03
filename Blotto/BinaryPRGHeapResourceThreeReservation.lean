import Blotto.BinaryPRGHeapResourceThreeStep
import Blotto.BinaryPRGHeapResourceReservation

/-! The rank-height physical three-coordinate loop has a decreasing tape
reservation, supplying its whole-run budget and successful-result invariant. -/

namespace Blotto.BinaryPRGHeapResourceThreeReservation
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGWordControllerBooleanResourceThreeWork (widthBound)
open BinaryPRGHeapResourceThreeStep (HeightInv)
open BinaryPRGHeapResourceUpdateBudget (growth updateBound)

variable {capacity : Store} {hCount : 3 = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,
  CanonicalWord (lookup capacity.tree address.word)}

def Reserved (C s P H : ℕ) (state : Finished capacity 3 hCount) : Prop :=
  HeightInv C s state ∧ state.heap.tape.length +
    state.active.length * growth capacity.width (widthBound C s) P ≤ H

def stepBound (C s depth indexWidth seedCap K H : ℕ) : ℕ :=
  max (BinaryPRGHeapResourceThreeStep.pairBound C s depth indexWidth seedCap K H)
    (updateBound K H depth (widthBound C s) 3)

theorem reserve_step {cells next active remaining G H : ℕ}
    (hReserve : cells + active * G ≤ H) (hGrowth : next ≤ cells + G)
    (hProgress : remaining < active) : next + remaining * G ≤ H := by
  have hm := Nat.mul_le_mul_right G (show remaining + 1 ≤ active by omega)
  rw [Nat.add_mul,one_mul] at hm
  omega

theorem reserved_room (C s P H : ℕ) (state : Finished capacity 3 hCount)
    (h : Reserved C s P H state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail) :
    state.heap.tape.length + growth capacity.width (widthBound C s) P ≤ H := by
  have ha : 1 ≤ state.active.length := by rw [he]; simp
  have hm := Nat.mul_le_mul_right (growth capacity.width (widthBound C s) P) ha
  simpa only [one_mul] using (Nat.add_le_add_left hm state.heap.tape.length).trans h.2

theorem reachableStepBudget (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (K H P : ℕ) (hK : limits.heap.tape.length ≤ K) (hP : 0 < P) (hRoom : H < 2^P) :
    BinaryPRGHeapResourceLoopBudget.ReachableStepBudget
      (capacity := capacity) (n := 3) (hCount := hCount) seed limits hC
      (Reserved (capacity := capacity) (hCount := hCount) C s P H)
      (stepBound C s capacity.width seed.width seed.cap.value K H) := by
  refine ⟨?_,?_,?_⟩
  · intro state first second tail he pc hp h
    have hHeap : state.heap.tape.length ≤ H := by have hh := h.2; omega
    exact (BinaryPRGHeapResourceThreeStep.pair_coin_bound (hC := hC)
      C s hs hCap seed limits state h.1 first second tail he pc hp K H hK hHeap).trans
      (le_max_left _ _)
  · intro state first second tail he branch h
    have hUpdate := BinaryPRGHeapResourceThreeStep.selectWithWork_bound
      C s hs hCap limits state h.1 first second tail he _
      (BinaryPRGHeapResourceLoop.pairWithWork_value (hC := hC) limits state first second tail he)
      branch K H P hK hP (reserved_room C s P H state h first second tail he) hRoom
    exact hUpdate.2.trans (le_max_right _ _)
  · intro state first second tail he branch h
    have hUpdate := BinaryPRGHeapResourceThreeStep.selectWithWork_bound
      C s hs hCap limits state h.1 first second tail he _
      (BinaryPRGHeapResourceLoop.pairWithWork_value (hC := hC) limits state first second tail he)
      branch K H P hK hP (reserved_room C s P H state h first second tail he) hRoom
    have hHeight := BinaryPRGHeapResourceThreeStep.selected_height
      C s hs hCap limits state h.1 first second tail he _
      (BinaryPRGHeapResourceLoop.pairWithWork_value (hC := hC) limits state first second tail he) branch
    have hProgress := BinaryPRGHeapResourceLoop.selectWithWork_progress limits state first second tail he _
      (BinaryPRGHeapResourceLoop.pairWithWork_value (hC := hC) limits state first second tail he) branch
    exact ⟨hHeight,reserve_step h.2 hUpdate.1 hProgress⟩

end Blotto.BinaryPRGHeapResourceThreeReservation
