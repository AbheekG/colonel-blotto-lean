import Blotto.BinaryPRGHeapLifetimeReservation

/-! Source-derived every-prefix retained allocation for both physical
resource loop regimes. Pointer room and step prices are derived internally
from the incoming tape, count, source width and seed parameters. -/

namespace Blotto.BinaryPRGHeapLoopSourceLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourceReservation (sourceSize sourcePointerWidth sourceHeapCap)
open BinaryPRGHeapLifetimeReservation (stepEnvelope)
set_option maxHeartbeats 1500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

def sourceEnvelope (count cells capCells depth pairW coinW indexWidth seedCap : ℕ) : ℕ :=
  count * (2 * stepEnvelope capCells (sourceHeapCap cells count depth pairW)
    depth pairW coinW indexWidth seedCap + 64) + 32

theorem lattice_usage (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity n hCount) (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    usage (BinaryPRGHeapLoopLifetime.runWithTrace seed limits hC state pc hp).2 ≤
      sourceEnvelope n state.heap.tape.length limits.heap.tape.length capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) (1 + 2 * binaryWordWidth D)
        seed.width seed.cap.value := by
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
  let P := sourcePointerWidth state.heap.tape.length n capacity.width W
  let H := sourceHeapCap state.heap.tape.length n capacity.width W
  have hP : 0 < P := by unfold P sourcePointerWidth; omega
  have hRoom : H < 2^P := BinaryPRGWordStoreHeap.quadratic_lt_capacity
    (sourceSize state.heap.tape.length n capacity.width W)
  have hInv := BinaryPRGHeapResourceReservation.source_reserved D state hs
  have hBudget := BinaryPRGHeapLifetimeReservation.lattice_budget (hC := hC) D hD hLattice hBox seed limits
    limits.heap.tape.length H P le_rfl hP hRoom
  have h := BinaryPRGHeapLoopLifetimeBudget.runWithTrace_usage seed limits hC _ _ hBudget state hInv pc hp
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ state.active_length_le) 32)

theorem height_usage {hCount3 : 3 = capacity.cap.value} (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount3).read j)) s)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity 3 hCount3) (hHeight : BinaryPRGHeapResourceThreeStep.HeightInv C s state)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    usage (BinaryPRGHeapLoopLifetime.runWithTrace seed limits hC state pc hp).2 ≤
      sourceEnvelope 3 state.heap.tape.length limits.heap.tape.length capacity.width
        (BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s) (BinaryThreeResourceHeight.coinWidth C s)
        seed.width seed.cap.value := by
  let W := BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s
  let P := sourcePointerWidth state.heap.tape.length 3 capacity.width W
  let H := sourceHeapCap state.heap.tape.length 3 capacity.width W
  have hP : 0 < P := by unfold P sourcePointerWidth; omega
  have hRoom : H < 2^P := BinaryPRGWordStoreHeap.quadratic_lt_capacity
    (sourceSize state.heap.tape.length 3 capacity.width W)
  have hInv : BinaryPRGHeapResourceThreeReservation.Reserved C s P H state := by
    refine ⟨hHeight,?_⟩
    have hm := Nat.mul_le_mul_right (BinaryPRGHeapResourceUpdateBudget.growth capacity.width W P) state.active_length_le
    exact (Nat.add_le_add_left hm _).trans (BinaryPRGHeapResourceReservation.source_room _ _ _ _)
  have hBudget := BinaryPRGHeapLifetimeReservation.height_budget (hC := hC) C s hs hCap seed limits
    limits.heap.tape.length H P le_rfl hP hRoom
  have h := BinaryPRGHeapLoopLifetimeBudget.runWithTrace_usage seed limits hC _ _ hBudget state hInv pc hp
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ state.active_length_le) 32)

theorem lattice_all_prefix (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity n hCount) (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (borrowed steps : ℕ) :
    let B := sourceEnvelope n state.heap.tape.length limits.heap.tape.length capacity.width
      (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) (1 + 2 * binaryWordWidth D) seed.width seed.cap.value
    retainedHeap borrowed (BinaryPRGHeapLoopLifetime.runWithTrace seed limits hC state pc hp).2 steps ≤ borrowed + B ∧
      framePeak ((BinaryPRGHeapLoopLifetime.runWithTrace seed limits hC state pc hp).2.take steps) ≤ B :=
  all_prefix _ _ (lattice_usage D hD hLattice hBox seed limits state hs pc hp) borrowed steps

theorem height_all_prefix {hCount3 : 3 = capacity.cap.value} (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount3).read j)) s)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity 3 hCount3) (hHeight : BinaryPRGHeapResourceThreeStep.HeightInv C s state)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (borrowed steps : ℕ) :
    let B := sourceEnvelope 3 state.heap.tape.length limits.heap.tape.length capacity.width
      (BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s) (BinaryThreeResourceHeight.coinWidth C s) seed.width seed.cap.value
    retainedHeap borrowed (BinaryPRGHeapLoopLifetime.runWithTrace seed limits hC state pc hp).2 steps ≤ borrowed + B ∧
      framePeak ((BinaryPRGHeapLoopLifetime.runWithTrace seed limits hC state pc hp).2.take steps) ≤ B :=
  all_prefix _ _ (height_usage C s hs hCap seed limits state hHeight pc hp) borrowed steps

end Blotto.BinaryPRGHeapLoopSourceLifetime
