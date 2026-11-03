import Blotto.BinaryPRGHeapLowerLifetime
import Blotto.BinaryPRGHeapLoopSourceLifetime

/-! Incoming physical tape lengths and the reflected rank-height invariant
derive deterministic lower completion's full retained reservation. An empty
seed is used only in erased proofs to reuse the stronger random-loop budget;
the lower producer itself has neither a seed argument nor a coin call. -/
namespace Blotto.BinaryPRGHeapLowerLifetimeBound
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage BinaryPRGHeapLowerLifetime
open BinaryPRGHeapResourceReservation (sourceSize sourcePointerWidth sourceHeapCap)
set_option maxHeartbeats 2000000
variable {capacity : Store} {hCount : 3 = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

def envelope (C s cells capCells depth : ℕ) : ℕ :=
  BinaryPRGHeapLoopSourceLifetime.sourceEnvelope 3 cells capCells depth
    (BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s) (BinaryThreeResourceHeight.coinWidth C s) 0 0

private theorem reserved (C s : ℕ) (state : Finished capacity 3 hCount)
    (hHeight : BinaryPRGHeapResourceThreeStep.HeightInv C s state) :
    BinaryPRGHeapResourceThreeReservation.Reserved C s
      (sourcePointerWidth state.heap.tape.length 3 capacity.width
        (BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s))
      (sourceHeapCap state.heap.tape.length 3 capacity.width
        (BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s)) state := by
  refine ⟨hHeight,?_⟩
  have hm := Nat.mul_le_mul_right
    (BinaryPRGHeapResourceUpdateBudget.growth capacity.width
      (BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s)
      (sourcePointerWidth state.heap.tape.length 3 capacity.width
        (BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s))) state.active_length_le
  exact (Nat.add_le_add_left hm _).trans (BinaryPRGHeapResourceReservation.source_room _ _ _ _)

theorem height_usage (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (limits : Stored capacity.tree) (state : Finished capacity 3 hCount)
    (hHeight : BinaryPRGHeapResourceThreeStep.HeightInv C s state) :
    usage (runWithTrace limits hC state).2 ≤ envelope C s state.heap.tape.length limits.heap.tape.length capacity.width := by
  let W := BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s
  let P := sourcePointerWidth state.heap.tape.length 3 capacity.width W
  let H := sourceHeapCap state.heap.tape.length 3 capacity.width W
  have hP : 0 < P := by unfold P sourcePointerWidth; omega
  have hRoom : H < 2^P := BinaryPRGWordStoreHeap.quadratic_lt_capacity (sourceSize state.heap.tape.length 3 capacity.width W)
  let seed := BinarySeedLookupTree.prepare []
  have hBudget := BinaryPRGHeapLifetimeReservation.height_budget (hC := hC) C s hs hCap seed limits
    limits.heap.tape.length H P le_rfl hP hRoom
  have hLower := budget_of_reachable seed limits hC _ _ hBudget
  have h := runWithTrace_usage limits hC _ _ hLower state (reserved C s state hHeight)
  have h' := h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ state.active_length_le) 32)
  exact h'

theorem height_returned (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (limits : Stored capacity.tree) (state : Finished capacity 3 hCount)
    (hHeight : BinaryPRGHeapResourceThreeStep.HeightInv C s state) :
    BinaryPRGHeapResourceThreeStep.HeightInv C s (runWithTrace limits hC state).1 ∧
      (runWithTrace limits hC state).1.heap.tape.length ≤
        sourceHeapCap state.heap.tape.length 3 capacity.width
          (BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s) := by
  let W := BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s
  let P := sourcePointerWidth state.heap.tape.length 3 capacity.width W
  let H := sourceHeapCap state.heap.tape.length 3 capacity.width W
  have hP : 0 < P := by unfold P sourcePointerWidth; omega
  have hRoom : H < 2^P := BinaryPRGWordStoreHeap.quadratic_lt_capacity (sourceSize state.heap.tape.length 3 capacity.width W)
  let seed := BinarySeedLookupTree.prepare []
  have hBudget := BinaryPRGHeapLifetimeReservation.height_budget (hC := hC) C s hs hCap seed limits
    limits.heap.tape.length H P le_rfl hP hRoom
  have hLower := budget_of_reachable seed limits hC _ _ hBudget
  have h := runWithTrace_invariant limits hC _ _ hLower state (reserved C s state hHeight)
  refine ⟨h.1,?_⟩
  change (runWithTrace limits hC state).1.heap.tape.length ≤ H
  have hh := h.2
  omega

theorem all_prefix (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (limits : Stored capacity.tree) (state : Finished capacity 3 hCount)
    (hHeight : BinaryPRGHeapResourceThreeStep.HeightInv C s state) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace limits hC state).2 steps ≤
      borrowed + envelope C s state.heap.tape.length limits.heap.tape.length capacity.width ∧
    framePeak ((runWithTrace limits hC state).2.take steps) ≤
      envelope C s state.heap.tape.length limits.heap.tape.length capacity.width :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (height_usage C s hs hCap limits state hHeight) borrowed steps

end Blotto.BinaryPRGHeapLowerLifetimeBound
