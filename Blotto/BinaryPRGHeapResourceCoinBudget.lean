import Blotto.BinaryPRGHeapResourcePairBudget
import Blotto.BinaryPRGHeapResourceLoopBudget

/-! The actual physical pair output feeds the indexed Boolean coin. Transfer
its probability word from the native lattice invariant without reducing the
physical pair implementation during the arithmetic width proof. -/

namespace Blotto.BinaryPRGHeapResourceCoinBudget
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,
  CanonicalWord (lookup capacity.tree address.word)}

theorem pair_probability_width (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j, OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hUnit : ∀ j, value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    width (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
      limits state first second tail he).1.probability ≤
      1 + 2 * binaryWordWidth D := by
  let choice := BinaryPRGHeapResourceLoop.logicalChoice (hC := hC)
    state first second tail he
  have hChoice : BinaryGeneralResourceLattice.StateInvariant
      (table capacity.cap capacity.tree n hCount) D choice.original.original.state := hs
  have hWidth := BinaryGeneralResourceLattice.choice_probability_wordWidth
    choice.original.original D hD hLattice hUnit hChoice
  have hWord : choice.outputs.probability = choice.original.original.probability :=
    (BinaryPRGWordControllerBooleanResourceLoop.Choice.probability_original choice).trans
      (BinaryPRGWordControllerGeneralChoice.Choice.probability_original choice.original)
  have hPhysical := congrArg
    (fun outputs : BinaryPRGWordControllerPairOutputs.Outputs => width outputs.probability)
    (BinaryPRGHeapResourceLoop.pairWithWork_value (hC := hC)
      limits state first second tail he)
  exact hPhysical.trans_le ((congrArg width hWord).le.trans hWidth)

theorem pair_sample_bound (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j, OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hUnit : ∀ j, value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity n hCount)
    (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryWordIndexCoinController.sample seed
      (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
        limits state first second tail he).1.probability pc hp).2 ≤
      BinaryWordIndexCoinController.sampleBound
        (1 + 2 * binaryWordWidth D) seed.width (seed.cap.value - pc.value) :=
  BinaryWordIndexCoinController.sample_bound seed _ pc hp _
    (pair_probability_width (hC := hC) D hD hLattice hUnit
      limits state hs first second tail he)

theorem pair_coin_lattice_bound (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j, OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hUnit : ∀ j, value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity n hCount)
    (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
      limits state first second tail he).2 +
      (BinaryWordIndexCoinController.sample seed
        (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
          limits state first second tail he).1.probability pc hp).2 + 8 ≤
      BinaryPRGWordControllerBooleanResourcePair.bound capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) +
      2 * BinaryPRGHeapStoredTree.readBound limits.heap.tape.length capacity.width +
      2 * BinaryPRGHeapStoredTree.readBound state.heap.tape.length capacity.width +
      BinaryWordIndexCoinController.sampleBound
        (1 + 2 * binaryWordWidth D) seed.width (seed.cap.value - pc.value) + 11 := by
  have hPair := BinaryPRGHeapResourcePairBudget.pairWithWork_lattice_bound
    (hC := hC) D hD hLattice hUnit limits state hs first second tail he
  have hCoin := pair_sample_bound (hC := hC) D hD hLattice hUnit
    seed limits state hs first second tail he pc hp
  omega

theorem pair_coin_seedBound (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j, OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hUnit : ∀ j, value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity n hCount)
    (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
      limits state first second tail he).2 +
      (BinaryWordIndexCoinController.sample seed
        (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
          limits state first second tail he).1.probability pc hp).2 + 8 ≤
      BinaryPRGWordControllerBooleanResourcePair.bound capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) +
      2 * BinaryPRGHeapStoredTree.readBound limits.heap.tape.length capacity.width +
      2 * BinaryPRGHeapStoredTree.readBound state.heap.tape.length capacity.width +
      BinaryWordIndexCoinController.sampleBound
        (1 + 2 * binaryWordWidth D) seed.width seed.cap.value + 11 := by
  have hPair := pair_coin_lattice_bound (hC := hC) D hD hLattice hUnit
    seed limits state hs first second tail he pc hp
  have hSpan := Nat.mul_le_mul_left
    (BinaryWordIndexCoinController.allowance (1 + 2 * binaryWordWidth D) seed.width)
    (Nat.add_le_add_right (Nat.sub_le seed.cap.value pc.value) 1)
  unfold BinaryWordIndexCoinController.sampleBound at *
  omega

theorem readBound_mono {first second depth : ℕ} (h : first ≤ second) :
    BinaryPRGHeapStoredTree.readBound first depth ≤
      BinaryPRGHeapStoredTree.readBound second depth := by
  have hm := BinaryPRGWordStoreHeapMachine.lookupBound_mono h
    (le_refl depth)
  unfold BinaryPRGHeapStoredTree.readBound
  omega

theorem pair_coin_heapBound (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j, OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hUnit : ∀ j, value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity n hCount)
    (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (C H : ℕ) (hCHeap : limits.heap.tape.length ≤ C)
    (hHHeap : state.heap.tape.length ≤ H) :
    (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
      limits state first second tail he).2 +
      (BinaryWordIndexCoinController.sample seed
        (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
          limits state first second tail he).1.probability pc hp).2 + 8 ≤
      BinaryPRGWordControllerBooleanResourcePair.bound capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) +
      2 * BinaryPRGHeapStoredTree.readBound C capacity.width +
      2 * BinaryPRGHeapStoredTree.readBound H capacity.width +
      BinaryWordIndexCoinController.sampleBound
        (1 + 2 * binaryWordWidth D) seed.width seed.cap.value + 11 := by
  have hPair := pair_coin_seedBound (hC := hC) D hD hLattice hUnit
    seed limits state hs first second tail he pc hp
  have hCap := readBound_mono (depth := capacity.width) hCHeap
  have hState := readBound_mono (depth := capacity.width) hHHeap
  omega

def boundedLatticeInv (D H : ℕ) (state : Finished capacity n hCount) : Prop :=
  BinaryPRGHeapResourceInvariant.latticeInv D state ∧
    state.heap.tape.length ≤ H

theorem reachableStepBudget (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j, OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hUnit : ∀ j, value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (C H M : ℕ) (hCHeap : limits.heap.tape.length ≤ C)
    (hM : BinaryPRGWordControllerBooleanResourcePair.bound capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) +
      2 * BinaryPRGHeapStoredTree.readBound C capacity.width +
      2 * BinaryPRGHeapStoredTree.readBound H capacity.width +
      BinaryWordIndexCoinController.sampleBound
        (1 + 2 * binaryWordWidth D) seed.width seed.cap.value + 11 ≤ M)
    (hSelected : ∀ (state : Finished capacity n hCount)
      (first second : Address capacity.width capacity.cap)
      (tail : List (Address capacity.width capacity.cap))
      (he : state.active = first :: second :: tail) (branch : Bool),
      boundedLatticeInv D H state →
      (BinaryPRGHeapResourceLoop.selectWithWork limits state first second tail he
        (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
          limits state first second tail he).1
        (BinaryPRGHeapResourceLoop.pairWithWork_value
          (hC := hC) limits state first second tail he) branch).2 ≤ M)
    (hHeap : ∀ (state : Finished capacity n hCount)
      (first second : Address capacity.width capacity.cap)
      (tail : List (Address capacity.width capacity.cap))
      (he : state.active = first :: second :: tail) (branch : Bool),
      boundedLatticeInv D H state →
      (BinaryPRGHeapResourceLoop.selectWithWork limits state first second tail he
        (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
          limits state first second tail he).1
        (BinaryPRGHeapResourceLoop.pairWithWork_value
          (hC := hC) limits state first second tail he) branch).1.heap.tape.length ≤ H) :
    BinaryPRGHeapResourceLoopBudget.ReachableStepBudget
      (capacity := capacity) (n := n) (hCount := hCount) seed limits hC
      (boundedLatticeInv (capacity := capacity) (n := n) (hCount := hCount) D H) M := by
  refine ⟨?_,hSelected,?_⟩
  · intro state first second tail he pc hp hs
    exact (pair_coin_heapBound (hC := hC) D hD hLattice hUnit seed limits
      state hs.1 first second tail he pc hp C H hCHeap hs.2).trans hM
  · intro state first second tail he branch hs
    exact ⟨BinaryPRGHeapResourceInvariant.selected_lattice (hC := hC)
        D hLattice limits state first second tail he _
        (BinaryPRGHeapResourceLoop.pairWithWork_value
          (hC := hC) limits state first second tail he) branch hs.1,
      hHeap state first second tail he branch hs⟩

end Blotto.BinaryPRGHeapResourceCoinBudget
