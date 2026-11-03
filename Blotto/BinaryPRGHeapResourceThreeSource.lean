import Blotto.BinaryPRGHeapResourceAt
import Blotto.BinaryPRGHeapResourceThreeReservation
import Blotto.BinaryPRGHeapResourceInputCost

/-! Original three-coordinate arrays and their height promises instantiate
the physical source, rank-height reservation and native three-state handoff
at any incoming absolute seed cursor. -/

namespace Blotto.BinaryPRGHeapResourceThreeSource
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerBooleanResourceThreeBridge
open BinaryPRGHeapResourceInputBounds (initialHeapBound preparationBound)
open BinaryPRGHeapResourceThreeReservation (Reserved)

def inputWidth (s : ℕ) : ℕ := BinaryPRGWordControllerBooleanResourceThreeWork.widthBound 2 s
def initialCells (s : ℕ) : ℕ := initialHeapBound 3 (inputWidth s)
def pointerWidth (s : ℕ) : ℕ :=
  BinaryPRGHeapResourceReservation.sourcePointerWidth (initialCells s) 3 (binaryWordWidth 3) (inputWidth s)
def heapCap (s : ℕ) : ℕ :=
  BinaryPRGHeapResourceReservation.sourceHeapCap (initialCells s) 3 (binaryWordWidth 3) (inputWidth s)
def loopBound (s indexWidth seedCap : ℕ) : ℕ :=
  3 * (2 * BinaryPRGHeapResourceThreeReservation.stepBound 2 s (binaryWordWidth 3)
    indexWidth seedCap (initialCells s) (heapCap s)) + 2
def bound (s indexWidth seedCap : ℕ) : ℕ :=
  preparationBound 3 (inputWidth s) + loopBound s indexWidth seedCap +
    BinaryPRGHeapResourceSourceReservation.terminalBound 3 (binaryWordWidth 3) (heapCap s) + 11

theorem stepBound_depth_mono {depth otherDepth C s indexWidth seedCap K H : ℕ}
    (hd : depth ≤ otherDepth) :
    BinaryPRGHeapResourceThreeReservation.stepBound C s depth indexWidth seedCap K H ≤
      BinaryPRGHeapResourceThreeReservation.stepBound C s otherDepth indexWidth seedCap K H := by
  have hk := BinaryPRGHeapResourceInputBounds.readBound_mono (a := K) le_rfl hd
  have hh := BinaryPRGHeapResourceInputBounds.readBound_mono (a := H) le_rfl hd
  have hPair : BinaryPRGHeapResourceThreeStep.pairBound C s depth indexWidth seedCap K H ≤
      BinaryPRGHeapResourceThreeStep.pairBound C s otherDepth indexWidth seedCap K H := by
    unfold BinaryPRGHeapResourceThreeStep.pairBound BinaryPRGWordControllerBooleanResourcePair.bound
    omega
  exact max_le_max hPair (BinaryPRGHeapResourceInputCost.updateBound_mono le_rfl le_rfl hd)

def sourceRun (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    BinaryPRGWordControllerThreeResource.Result seed capacity × ℕ :=
  let drawn := BinaryPRGHeapResourceAt.nativeAt seed capacity resource hC hR pc hp
  ((drawn.1.1.map generalCertified_toThree,drawn.1.2),drawn.2 + 4)

theorem sourceRun_erasure (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceRun seed capacity resource hC hR pc hp).1 =
      BinaryPRGWordControllerThreeResource.run seed capacity hC
        (BinaryThreeResourcePair.initial capacity resource hC hR) pc hp := by
  change result_toThree seed capacity (BinaryPRGHeapResourceAt.nativeAt
    seed capacity resource hC hR pc hp).1 = _
  rw [BinaryPRGHeapResourceAt.nativeAt_erasure,run_toThree,general_toThree_initial]

theorem sourceRun_bound (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceRun seed capacity resource hC hR pc hp).2 ≤ bound s seed.width seed.cap.value := by
  let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
  let cap := BinaryPRGHeapResourceSource.capStore capacity
  let W := inputWidth s
  let K := initialCells s
  let P := pointerWidth s
  let H := heapCap s
  have hW : 1 ≤ W := by unfold W inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound; omega
  have hHeight := expressionHeightBudget_ge_input s (3 * 2)
  have hcWidth : ∀ j,width (capacity.read j) ≤ W := by
    intro j
    have hw := (hC j).2.trans (rationalWordWidth_of_height (hCapacity j))
    unfold W inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound BinaryThreeResourceHeight.resourceHeight
    omega
  have hrWidth : ∀ j,width (resource.read j) ≤ W := by
    intro j
    have hw := (hR j).2.trans (rationalWordWidth_of_height (hResource j))
    unfold W inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound BinaryThreeResourceHeight.resourceHeight
    omega
  have hInitial := BinaryPRGHeapResourceInputBounds.initialWithWork_input_bound
    capacity resource hC hR W hW hcWidth hrWidth
  have hHeaps := BinaryPRGHeapResourceInputBounds.initial_heaps_bound
    capacity resource hC hR W hW hcWidth hrWidth
  change prepared.1.1.heap.tape.length ≤ K ∧ prepared.1.2.heap.tape.length ≤ K at hHeaps
  have hd := BinaryPRGHeapResourceInputBounds.source_depth capacity
  change cap.width ≤ binaryWordWidth 3 at hd
  have hCap : ∀ j,RationalHeight (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
      cap.cap cap.tree 3 (BinaryPRGHeapResourceSource.count capacity)).read j)) s := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hCapacity
  have hState : BinaryPRGHeapResourceThreeStep.HeightInv 2 s prepared.1.2 := by
    unfold BinaryPRGHeapResourceThreeStep.HeightInv
    rw [BinaryPRGHeapResourceSource.initialWithWork_reference]
    exact BinaryPRGWordControllerBooleanResourceThreeWork.source_initial_height
      capacity resource hC hR s hResource
  have hGrowth : BinaryPRGHeapResourceUpdateBudget.growth cap.width W P ≤
      BinaryPRGHeapResourceUpdateBudget.growth (binaryWordWidth 3) W P := by
    unfold BinaryPRGHeapResourceUpdateBudget.growth
    gcongr
  have hReserved : Reserved 2 s P H prepared.1.2 := by
    refine ⟨hState,?_⟩
    have hm := Nat.mul_le_mul prepared.1.2.active_length_le hGrowth
    exact (Nat.add_le_add hHeaps.2 hm).trans
      (BinaryPRGHeapResourceReservation.source_room K 3 (binaryWordWidth 3) W)
  have hP : 0 < P := by unfold P pointerWidth BinaryPRGHeapResourceReservation.sourcePointerWidth; omega
  have hRoom : H < 2^P := BinaryPRGWordStoreHeap.quadratic_lt_capacity _
  have hBudget := BinaryPRGHeapResourceThreeReservation.reachableStepBudget
    (hC := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    2 s hs hCap seed prepared.1.1 K H P hHeaps.1 hP hRoom
  have hLoop := BinaryPRGHeapResourceLoopBudget.runWithWork_inputCount_bound seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    (Reserved 2 s P H) _ hBudget prepared.1.2 hReserved pc hp
  have hLoop' := hLoop.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3
    (Nat.mul_le_mul_left 2 (stepBound_depth_mono hd))) 2)
  change (BinaryPRGHeapResourceLoop.runWithWork seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    prepared.1.2 pc hp).2 ≤ loopBound s seed.width seed.cap.value at hLoop'
  have hReturned : ∀ state : BinaryPRGHeapResourceLoop.Finished cap 3
      (BinaryPRGHeapResourceSource.count capacity),
      (BinaryPRGHeapResourceAt.sourceAt seed capacity resource hC hR pc hp).1.2.1 = some state →
      state.heap.tape.length ≤ H := by
    intro state hSome
    have hh := BinaryPRGHeapResourceLoopBudget.runWithWork_invariant seed prepared.1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
      (Reserved 2 s P H) _ hBudget prepared.1.2 hReserved pc hp state hSome
    have hh' := hh.2
    omega
  have hNative := BinaryPRGHeapResourceAt.nativeAt_bound seed capacity resource hC hR pc hp
    (preparationBound 3 W) (loopBound s seed.width seed.cap.value) H hInitial hLoop' hReturned
  change (BinaryPRGHeapResourceAt.nativeAt seed capacity resource hC hR pc hp).2 ≤
    preparationBound 3 W + loopBound s seed.width seed.cap.value +
      BinaryPRGHeapResourceSourceReservation.terminalBound 3 cap.width H + 7 at hNative
  have hTerminal := BinaryPRGHeapResourceInputCost.terminalBound_mono (count := 3) hd (le_refl H)
  unfold sourceRun bound
  dsimp only
  change _ + 4 ≤ preparationBound 3 W + loopBound s seed.width seed.cap.value +
    BinaryPRGHeapResourceSourceReservation.terminalBound 3 (binaryWordWidth 3) H + 11
  omega

end Blotto.BinaryPRGHeapResourceThreeSource
