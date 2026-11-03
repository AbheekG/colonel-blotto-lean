import Blotto.BinaryPRGHeapResourceLoop
import Blotto.BinaryPRGHeapResourceSource
import Blotto.BinaryGeneralResourceLattice

/-! The native rational-lattice resource invariant transported through an
actual physical heap selection. This is one component of a future physical
work/space invariant; it does not itself bound the tape heap. -/

namespace Blotto.BinaryPRGHeapResourceInvariant
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,
  CanonicalWord (lookup capacity.tree address.word)}

def latticeInv (D : ℕ) (state : Finished capacity n hCount) : Prop :=
  BinaryGeneralResourceLattice.StateInvariant
    (table capacity.cap capacity.tree n hCount) D state.reference.reference

theorem selected_lattice (D : ℕ)
    (hLattice : ∀ j,OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs =
      (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC)
        state first second tail he).outputs)
    (branch : Bool) (hs : latticeInv D state) :
    latticeInv D (BinaryPRGHeapResourceLoop.selectWithWork limits state
      first second tail he outputs hOutputs branch).1 := by
  let choice := BinaryPRGHeapResourceLoop.logicalChoice (hC := hC)
    state first second tail he
  have hChoice : BinaryGeneralResourceLattice.StateInvariant
      (table capacity.cap capacity.tree n hCount) D choice.original.original.state := hs
  have hNext := BinaryGeneralResourceLattice.choice_select_invariant
    choice.original.original D hLattice hChoice branch
  unfold latticeInv
  rw [BinaryPRGHeapResourceLoop.selectWithWork_reference
    limits state first second tail he outputs hOutputs branch]
  rw [choice.select_original,choice.original.select_original]
  exact hNext

theorem lattice_transport {m : ℕ} {first second : FixedArrayTable m SignedWord}
    (D : ℕ) (h : first = second) (state : BinaryResourcePair.Certified first) :
    BinaryGeneralResourceLattice.StateInvariant first D state ↔
      BinaryGeneralResourceLattice.StateInvariant second D
        (BinaryPRGWordControllerBooleanResourceSource.transport h state) := by
  subst second
  rfl

theorem initial_lattice {m : ℕ} (capacity resource : FixedArrayTable m SignedWord)
    (hCanonicalCapacity : ∀ j,CanonicalWord (capacity.read j))
    (hCanonicalResource : ∀ j,CanonicalWord (resource.read j))
    (D : ℕ)
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧
      value (resource.read j) ≤ value (capacity.read j)) :
    latticeInv D
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource
        hCanonicalCapacity hCanonicalResource).1.2 := by
  have hNative := BinaryGeneralResourceLattice.initial_invariant capacity resource
    hCanonicalCapacity hCanonicalResource D hResourceLattice hResourceBox
  have hTransfer : BinaryGeneralResourceLattice.StateInvariant capacity D
      (BinaryPRGWordControllerBooleanResourceSource.transport
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
        (BinaryPRGWordControllerBooleanResourceSource.initial capacity resource
          hCanonicalCapacity hCanonicalResource).reference) := by
    rw [BinaryPRGWordControllerBooleanResourceSource.initial_reference]
    exact hNative
  have hPulled := (lattice_transport D
    (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
    (BinaryPRGWordControllerBooleanResourceSource.initial capacity resource
      hCanonicalCapacity hCanonicalResource).reference).mpr hTransfer
  unfold latticeInv
  rw [BinaryPRGHeapResourceSource.initialWithWork_reference]
  exact hPulled

end Blotto.BinaryPRGHeapResourceInvariant
