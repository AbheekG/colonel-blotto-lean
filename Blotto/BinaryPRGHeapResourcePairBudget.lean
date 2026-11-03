import Blotto.BinaryPRGHeapResourceLoop
import Blotto.BinaryPRGWordControllerBooleanResourceLoopWork
import Blotto.BinaryPRGHeapResourceInvariant

/-! Compare the four physical tape reads in one pair preparation with the
earlier lattice-bounded logical pair price. The comparison retains the same
actual arithmetic payload and outputs. -/

namespace Blotto.BinaryPRGHeapResourcePairBudget
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,
  CanonicalWord (lookup capacity.tree address.word)}

theorem pairWithWork_readBound (limits : Stored capacity.tree)
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
      limits state first second tail he).2 ≤
      (BinaryPRGWordControllerBooleanResourcePair.pairWithWork
        capacity.tree state.reference.state first second tail hC
        state.reference.canonical state.reference.interior
        (state.certified.choose_spec.2.symm.trans he)).2 +
      2 * BinaryPRGHeapStoredTree.readBound limits.heap.tape.length capacity.width +
      2 * BinaryPRGHeapStoredTree.readBound state.heap.tape.length capacity.width + 3 := by
  let a := BinaryPRGHeapStoredTree.readWithWork limits first.word
  let b := BinaryPRGHeapStoredTree.readWithWork limits second.word
  let c := state.packed.readWithWork first.word
  let d := state.packed.readWithWork second.word
  have ha := (BinaryPRGHeapStoredTree.readWithWork_bounds limits first.word).1
  have hb := (BinaryPRGHeapStoredTree.readWithWork_bounds limits second.word).1
  have hc := state.packed.readWithWork_bounds first.word
  have hd := state.packed.readWithWork_bounds second.word
  change a.2.work ≤ BinaryPRGHeapStoredTree.readBound
    limits.heap.tape.length capacity.width at ha
  change b.2.work ≤ BinaryPRGHeapStoredTree.readBound
    limits.heap.tape.length capacity.width at hb
  change c.2.work ≤ BinaryPRGHeapStoredTree.readBound
    state.heap.tape.length capacity.width at hc
  change d.2.work ≤ BinaryPRGHeapStoredTree.readBound
    state.heap.tape.length capacity.width at hd
  have hSource := BinaryPRGHeapResourceLoop.sourceWithWork_value
    (hC := hC) limits state first second tail he
  unfold BinaryPRGHeapResourceLoop.pairWithWork
    BinaryPRGWordControllerBooleanResourcePair.pairWithWork
  dsimp only
  rw [hSource]
  change a.2.work + b.2.work + c.2.work + d.2.work + 8 +
    (BinaryPRGWordControllerBooleanResourcePair.source capacity.tree
      state.reference.state first second tail hC state.reference.canonical
      state.reference.interior (state.certified.choose_spec.2.symm.trans he)).sourcePayloadWork +
    (BinaryPRGWordControllerPairOutputs.prepareWithWork
      (BinaryPRGWordControllerBooleanResourcePair.source capacity.tree
        state.reference.state first second tail hC state.reference.canonical
        state.reference.interior (state.certified.choose_spec.2.symm.trans he))).2 + 4 ≤ _
  omega

theorem pairWithWork_lattice_bound (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D
      (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        capacity.cap capacity.tree n hCount).read j)))
    (hUnit : ∀ j,value ((BinaryPRGWordControllerBooleanResourceUpdate.table
      capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
      limits state first second tail he).2 ≤
      BinaryPRGWordControllerBooleanResourcePair.bound capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) +
      2 * BinaryPRGHeapStoredTree.readBound limits.heap.tape.length capacity.width +
      2 * BinaryPRGHeapStoredTree.readBound state.heap.tape.length capacity.width + 3 := by
  have hRead := pairWithWork_readBound (hC := hC)
    limits state first second tail he
  have hActive : state.reference.state.active = first :: second :: tail :=
    state.certified.choose_spec.2.symm.trans he
  have hNative : state.reference.reference.state.active =
      first.index n hCount :: second.index n hCount ::
        tail.map (fun address => address.index n hCount) := by
    rw [state.reference.reference_state]
    simp only [BinaryPRGWordControllerBooleanResourceUpdate.State.reference,
      hActive, List.map_cons]
  have hTrace := BinaryGeneralResourceLattice.pair_trace_wordBounds
    (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC)
    state.reference.reference (first.index n hCount) (second.index n hCount)
    (tail.map (fun address => address.index n hCount)) hNative
    D hD hLattice hUnit hs
  rw [← BinaryPRGWordControllerBooleanResourcePair.source_reference
    capacity.tree state.reference.state first second tail hC state.reference.canonical
    state.reference.interior hActive n hCount
    (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC)
    state.reference.reference state.reference.reference_state] at hTrace
  have hPair := BinaryPRGWordControllerBooleanResourcePair.pairWithWork_bound
    capacity.tree state.reference.state first second tail hC
    state.reference.canonical state.reference.interior hActive
    (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) hTrace
  omega

end Blotto.BinaryPRGHeapResourcePairBudget
