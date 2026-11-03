import Blotto.BinaryPRGHeapResourceCoinBudget
import Blotto.BinaryPRGHeapWriteSequence

/-! Prices and reservation bounds for the actual two persistent writes and
the physical two-address rescan of a selected resource update. -/

namespace Blotto.BinaryPRGHeapResourceUpdateBudget
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapPackedStore (Packed)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)

def growth (depth W P : ℕ) : ℕ := 2 * (depth + 1 + 2 * W) * (4 * P + 5)

theorem twoWrites_controlled {depth : ℕ} (data : Packed depth)
    (first second : FixedBinaryWord depth) (chosen other : SignedWord)
    (W P H : ℕ) (hChosen : width chosen ≤ W) (hOther : width other ≤ W)
    (hP : 0 < P) (hSpace : data.heap.tape.length + growth depth W P ≤ H)
    (hRoom : H < 2^P) :
    let a := data.writeWithWork first chosen
    let b := a.1.writeWithWork second other
    b.1.heap.tape.length ≤ data.heap.tape.length + growth depth W P ∧
      a.2.work + b.2.work ≤ 2 * BinaryPRGWordStoreHeapMachine.patchBound H depth := by
  let changes : List (BinaryPRGHeapWriteSequence.Change depth) :=
    [(first,chosen),(second,other)]
  have hcn : chosen.numerator.length ≤ W := (Nat.le_max_left _ _).trans hChosen
  have hcd : chosen.denominator.length ≤ W := (Nat.le_max_right _ _).trans hChosen
  have hon : other.numerator.length ≤ W := (Nat.le_max_left _ _).trans hOther
  have hod : other.denominator.length ≤ W := (Nat.le_max_right _ _).trans hOther
  have hPayload : BinaryPRGHeapWriteSequence.totalPayload changes ≤
      2 * (depth + 1 + 2 * W) := by
    simp only [changes,BinaryPRGHeapWriteSequence.totalPayload,
      BinaryPRGHeapWriteSequence.payloadCost,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil]
    omega
  have hRange : BinaryPRGHeapWriteSequence.range data changes P ≤
      data.heap.tape.length + growth depth W P := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_right (4 * P + 5) hPayload) _
  have h := BinaryPRGHeapWriteSequence.executeWithWork_controlled data changes P hP
    ((hRange.trans hSpace).trans_lt hRoom)
  have hm := BinaryPRGHeapStoredTree.patchBound_mono (hRange.trans hSpace) depth
  let a := data.writeWithWork first chosen
  let b := a.1.writeWithWork second other
  change b.1.heap.tape.length ≤ BinaryPRGHeapWriteSequence.range data changes P ∧
    a.2.work + b.2.work + 9 ≤
      2 * (BinaryPRGWordStoreHeapMachine.patchBound
        (BinaryPRGHeapWriteSequence.range data changes P) depth + 4) + 1 ∧
    _ at h
  change b.1.heap.tape.length ≤ data.heap.tape.length + growth depth W P ∧
    a.2.work + b.2.work ≤ 2 * BinaryPRGWordStoreHeapMachine.patchBound H depth
  exact ⟨h.1.trans hRange,by omega⟩

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

def testBound (C H depth W : ℕ) : ℕ :=
  BinaryPRGHeapStoredTree.readBound H depth +
    BinaryPRGHeapStoredTree.readBound C depth + 1000 * (W + 1)^2 + 6

def scanBound (C H depth W count : ℕ) : ℕ :=
  count * (testBound C H depth W + 2 * (depth + 1) + 3) + 1

theorem fractionalWithWork_bound (limits : Stored capacity.tree)
    (bids : Packed capacity.width) (address : Address capacity.width capacity.cap)
    (C H W : ℕ) (hC : limits.heap.tape.length ≤ C)
    (hH : bids.heap.tape.length ≤ H) (hW : 1 ≤ W)
    (hBid : width (bids.readWithWork address.word).1 ≤ W)
    (hLimit : width (BinaryPRGHeapStoredTree.readWithWork limits address.word).1 ≤ W) :
    (BinaryPRGHeapResourceLoop.fractionalWithWork limits bids address).2 ≤
      testBound C H capacity.width W := by
  have h := BinaryPRGHeapResourceLoop.fractionalWithWork_bound limits bids address
  have hb := BinaryPRGHeapResourceCoinBudget.readBound_mono
    (depth := capacity.width) hH
  have hc := BinaryPRGHeapResourceCoinBudget.readBound_mono
    (depth := capacity.width) hC
  have hw0 : BinaryRationalArithmetic.pairWidth
      (bids.readWithWork address.word).1 BinaryRationalOpcode.zero ≤ W := by
    exact max_le hBid (by change 1 ≤ W; exact hW)
  have hw1 : BinaryRationalArithmetic.pairWidth
      (BinaryPRGHeapStoredTree.readWithWork limits address.word).1
      (bids.readWithWork address.word).1 ≤ W := max_le hLimit hBid
  have hp0 := Nat.pow_le_pow_left (Nat.add_le_add_right hw0 1) 2
  have hp1 := Nat.pow_le_pow_left (Nat.add_le_add_right hw1 1) 2
  unfold BinaryPRGHeapResourceLoop.fractionalWorkBound
    BinaryPRGHeapResourceLoop.fractionalWorkBoundRaw at h
  dsimp only at h
  rw [address.word.size] at h
  unfold testBound
  omega

theorem scanWithWork_bound (limits : Stored capacity.tree)
    (bids : Packed capacity.width) (addresses : List (Address capacity.width capacity.cap))
    (C H W : ℕ) (hC : limits.heap.tape.length ≤ C)
    (hH : bids.heap.tape.length ≤ H) (hW : 1 ≤ W)
    (hBid : ∀ address : Address capacity.width capacity.cap,
      width (bids.readWithWork address.word).1 ≤ W)
    (hLimit : ∀ address : Address capacity.width capacity.cap,
      width (BinaryPRGHeapStoredTree.readWithWork limits address.word).1 ≤ W) :
    (BinaryPRGHeapResourceLoop.scanWithWork limits bids addresses).2 ≤
      scanBound C H capacity.width W addresses.length := by
  induction addresses with
  | nil => simp [BinaryPRGHeapResourceLoop.scanWithWork,scanBound]
  | cons address rest ih =>
      have ht := fractionalWithWork_bound limits bids address C H W hC hH hW
        (hBid address) (hLimit address)
      simp only [BinaryPRGHeapResourceLoop.scanWithWork]
      unfold scanBound at *
      rw [address.word.size]
      simp only [List.length_cons]
      nlinarith

def updateBound (C H depth W count : ℕ) : ℕ :=
  2 * BinaryPRGHeapStoredTree.readBound H depth + 22000 * (W + 1)^2 +
    2 * BinaryPRGWordStoreHeapMachine.patchBound H depth +
    scanBound C H depth W 2 + 2 * (depth + 1) * (count + 2) + 12

theorem updateWithWork_bound (limits : Stored capacity.tree)
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (chosen : SignedWord)
    (C H W P count : ℕ) (hC : limits.heap.tape.length ≤ C)
    (hW : 1 ≤ W) (hP : 0 < P)
    (hSpace : state.heap.tape.length + growth capacity.width W P ≤ H)
    (hRoom : H < 2^P) (hLength : tail.length ≤ count)
    (hOld : ∀ address : Address capacity.width capacity.cap,
      width (state.packed.readWithWork address.word).1 ≤ W)
    (hLimit : ∀ address : Address capacity.width capacity.cap,
      width (BinaryPRGHeapStoredTree.readWithWork limits address.word).1 ≤ W)
    (hChosen : width chosen ≤ W) :
    let a := state.packed.readWithWork first.word
    let b := state.packed.readWithWork second.word
    let total := BinaryQuadraticOpcode.applyWithWork .add a.1 b.1
    let other := BinaryQuadraticOpcode.applyWithWork .sub total.1 chosen
    let next := ((state.packed.writeWithWork first.word chosen).1.writeWithWork
      second.word other.1).1
    width total.1 ≤ W → width other.1 ≤ W →
    (∀ address : Address capacity.width capacity.cap,
      width (next.readWithWork address.word).1 ≤ W) →
    (BinaryPRGHeapResourceLoop.updateWithWork limits state
      first second tail chosen).1.1.heap.tape.length ≤
        state.heap.tape.length + growth capacity.width W P ∧
      (BinaryPRGHeapResourceLoop.updateWithWork limits state
        first second tail chosen).2 ≤ updateBound C H capacity.width W count := by
  dsimp only
  intro hTotal hOther hNext
  let a := state.packed.readWithWork first.word
  let b := state.packed.readWithWork second.word
  let total := BinaryQuadraticOpcode.applyWithWork .add a.1 b.1
  let other := BinaryQuadraticOpcode.applyWithWork .sub total.1 chosen
  let intermediate := state.packed.writeWithWork first.word chosen
  let next := intermediate.1.writeWithWork second.word other.1
  have hWrites := twoWrites_controlled state.packed first.word second.word
    chosen other.1 W P H hChosen hOther hP hSpace hRoom
  change next.1.heap.tape.length ≤ state.heap.tape.length + growth capacity.width W P ∧
    intermediate.2.work + next.2.work ≤
      2 * BinaryPRGWordStoreHeapMachine.patchBound H capacity.width at hWrites
  have hNextHeap : next.1.heap.tape.length ≤ H := hWrites.1.trans hSpace
  have hInitialHeap : state.packed.heap.tape.length ≤ H := by
    change state.heap.tape.length ≤ H
    omega
  have hScan := scanWithWork_bound limits next.1 [first,second]
    C H W hC hNextHeap hW hNext hLimit
  have hReadA := (state.packed.readWithWork_bounds first.word).trans
    (BinaryPRGHeapResourceCoinBudget.readBound_mono hInitialHeap)
  have hReadB := (state.packed.readWithWork_bounds second.word).trans
    (BinaryPRGHeapResourceCoinBudget.readBound_mono hInitialHeap)
  have hAdd := BinaryQuadraticOpcode.applyWithWork_bound .add a.1 b.1
  have hSub := BinaryQuadraticOpcode.applyWithWork_bound .sub total.1 chosen
  have hAddWidth : BinaryRationalArithmetic.pairWidth a.1 b.1 ≤ W :=
    max_le (hOld first) (hOld second)
  have hSubWidth : BinaryRationalArithmetic.pairWidth total.1 chosen ≤ W :=
    max_le hTotal hChosen
  have hAddPow := Nat.pow_le_pow_left (Nat.add_le_add_right hAddWidth 1) 2
  have hSubPow := Nat.pow_le_pow_left (Nat.add_le_add_right hSubWidth 1) 2
  have hAppend := Nat.mul_le_mul_left (2 * (capacity.width + 1))
    (Nat.add_le_add_right hLength 2)
  change a.2.work ≤ _ at hReadA
  change b.2.work ≤ _ at hReadB
  change total.2 ≤ _ at hAdd
  change other.2 ≤ _ at hSub
  change next.1.heap.tape.length ≤ state.heap.tape.length + growth capacity.width W P ∧
    a.2.work + b.2.work + total.2 + other.2 + intermediate.2.work + next.2.work +
      (BinaryPRGHeapResourceLoop.scanWithWork limits next.1 [first,second]).2 +
      2 * (first.word.bits.length + 1) * (tail.length + 2) + 12 ≤ _
  rw [first.word.size]
  change (BinaryPRGHeapResourceLoop.scanWithWork limits next.1 [first,second]).2 ≤
    scanBound C H capacity.width W 2 at hScan
  unfold updateBound
  exact ⟨hWrites.1,by omega⟩

variable {hC : ∀ address : Address capacity.width capacity.cap,
  CanonicalWord (lookup capacity.tree address.word)}

theorem selectWithWork_lattice_bound (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice
      (hC := hC) state first second tail he).outputs) (branch : Bool)
    (C H P : ℕ) (hCHeap : limits.heap.tape.length ≤ C) (hP : 0 < P)
    (hSpace : state.heap.tape.length + growth capacity.width
      (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) P ≤ H)
    (hRoom : H < 2^P) :
    (BinaryPRGHeapResourceLoop.selectWithWork limits state first second tail he
      outputs hOutputs branch).1.heap.tape.length ≤
        state.heap.tape.length + growth capacity.width
          (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) P ∧
      (BinaryPRGHeapResourceLoop.selectWithWork limits state first second tail he
        outputs hOutputs branch).2 ≤ updateBound C H capacity.width
          (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) n := by
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
  let choice := BinaryPRGHeapResourceLoop.logicalChoice (hC := hC)
    state first second tail he
  let chosen := if branch then outputs.upper else outputs.lower
  let a := state.packed.readWithWork first.word
  let b := state.packed.readWithWork second.word
  let total := BinaryQuadraticOpcode.applyWithWork .add a.1 b.1
  let other := BinaryQuadraticOpcode.applyWithWork .sub total.1 chosen
  let selected := BinaryPRGHeapResourceLoop.selectWithWork limits state
    first second tail he outputs hOutputs branch
  have hu := fun j => (hBox j).2
  have hChosenEq : chosen = choice.endpoint branch := by
    dsimp only [chosen,BinaryPRGWordControllerBooleanResourceLoop.Choice.endpoint]
    rw [hOutputs]
  have hChoice : BinaryGeneralResourceLattice.StateInvariant
      (table capacity.cap capacity.tree n hCount) D choice.original.original.state := hs
  have hChosenNative := BinaryGeneralResourceExecution.selected_endpoint_width
    choice.original.original D hD hLattice hu hChoice branch
  rw [← choice.original.endpoint_original,← choice.endpoint_original] at hChosenNative
  have hChosenWidth : width chosen ≤ W := by
    rw [hChosenEq]
    unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    omega
  have hTotalNative := BinaryGeneralResourceExecution.selected_total_width
    choice.original.original D hD hLattice hu hChoice
  have hOtherNative := BinaryGeneralResourceExecution.selected_other_width
    choice.original.original D hD hLattice hu hChoice branch
  rw [← choice.original.endpoint_original,← choice.endpoint_original] at hOtherNative
  simp only [BinaryPRGWordControllerGeneralChoice.Choice.original,
    BinaryPRGWordControllerBooleanResourceLoop.Choice.original,
    BinaryPRGWordControllerBooleanResourceLoop.Certified.reference_state,
    BinaryPRGWordControllerBooleanResourceUpdate.State.reference,
    BinaryPRGWordControllerBooleanResourceUpdate.table_read] at hTotalNative hOtherNative
  have hReadA := BinaryPRGHeapPackedStore.Packed.readWithWork_value
    state.packed state.packed_realizes first.word
  have hReadB := BinaryPRGHeapPackedStore.Packed.readWithWork_value
    state.packed state.packed_realizes second.word
  have hA : BinaryRationalOpcode.Valid a.1 := by
    rw [hReadA]; exact (state.reference.canonical first).1
  have hB : BinaryRationalOpcode.Valid b.1 := by
    rw [hReadB]; exact (state.reference.canonical second).1
  have hAdd := BinaryQuadraticOpcode.applyWithWork_state .add a.1 b.1 hA hB
  have hTotalValid : BinaryRationalOpcode.Valid total.1 := by
    rw [hAdd]
    exact BinaryRationalOpcode.apply_valid .add _ _ hA hB
  have hChosenValid : BinaryRationalOpcode.Valid chosen := by
    rw [hChosenEq]; exact (choice.endpoint_canonical branch).1
  have hSub := BinaryQuadraticOpcode.applyWithWork_state .sub
    total.1 chosen hTotalValid hChosenValid
  have hTotalWidth : width total.1 ≤ W := by
    rw [hAdd,hReadA,hReadB]
    exact hTotalNative
  have hOtherWidth : width other.1 ≤ W := by
    rw [hSub,hAdd,hReadA,hReadB,hChosenEq]
    exact hOtherNative.trans (by
      unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      omega)
  have hOld : ∀ address : Address capacity.width capacity.cap,
      width (state.packed.readWithWork address.word).1 ≤ W := by
    intro address
    rw [BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes]
    exact BinaryPRGWordControllerBooleanResourceLoopWork.state_width
      D hD state.reference hu hs address
  have hLimit : ∀ address : Address capacity.width capacity.cap,
      width (BinaryPRGHeapStoredTree.readWithWork limits address.word).1 ≤ W := by
    intro address
    rw [BinaryPRGHeapStoredTree.readWithWork_value]
    exact BinaryPRGWordControllerBooleanResourceLoopWork.capacity_width
      D hD hC hLattice hBox address
  have hSelectedInv := BinaryPRGHeapResourceInvariant.selected_lattice
    (hC := hC) D hLattice limits state first second tail he outputs hOutputs branch hs
  have hNext : ∀ address : Address capacity.width capacity.cap,
      width (selected.1.packed.readWithWork address.word).1 ≤ W := by
    intro address
    rw [BinaryPRGHeapPackedStore.Packed.readWithWork_value
      selected.1.packed selected.1.packed_realizes]
    exact BinaryPRGWordControllerBooleanResourceLoopWork.state_width
      D hD selected.1.reference hu hSelectedInv address
  have hLength : tail.length ≤ n := by
    have hn := state.active_length_le
    rw [he] at hn
    simp only [List.length_cons] at hn
    omega
  have hUpdate := updateWithWork_bound limits state first second tail chosen C H W P n
    hCHeap (by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega)
    hP hSpace hRoom hLength hOld hLimit hChosenWidth
    hTotalWidth hOtherWidth hNext
  exact hUpdate

end Blotto.BinaryPRGHeapResourceUpdateBudget
