import Blotto.BinaryAddressFormationWork
import Blotto.BinaryRouteSlotReadingWork

/-! Actual finite-region addresses have a Boolean formation implementation.
Formation and existing access prices compose for route builds and slot reads.
The resulting symbolic ledger still has explicit primitive/allocator contracts. -/

namespace Blotto.FixedWordRegion

def formationWork {n W : ℕ} (primitive : ℕ → ℕ) (address : Fin (n * W)) : ℕ :=
  let pair := finProdFinEquiv.symm address
  BinaryAddressFormation.encodedWork primitive 0 pair.1 pair.2

theorem formationWork_bound {n W : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (address : Fin (n * W)) : formationWork primitive address ≤ BinaryAddressFormation.encodedWorkBound c 0 n W :=
  BinaryAddressFormation.encodedWork_bound primitive c hPrimitive 0 (finProdFinEquiv.symm address).1 (finProdFinEquiv.symm address).2

theorem formedAddress_value {n W : ℕ} (address : Fin (n * W)) :
    BinaryBigEndian.littleValue (BinaryAddressFormation.encodedAddress 0 (finProdFinEquiv.symm address).1 (finProdFinEquiv.symm address).2) = address.val := by
  rw [BinaryAddressFormation.encodedAddress_value]
  change 0 + (finProdFinEquiv (finProdFinEquiv.symm address)).val = address.val
  rw [Equiv.apply_symm_apply, Nat.zero_add]

def formedAccessWork {n W : ℕ} (primitive : ℕ → ℕ) (address : Fin (n * W)) : ℕ :=
  formationWork primitive address + accessWork primitive address.val

def formedAccessBound (c n W : ℕ) : ℕ := BinaryAddressFormation.encodedWorkBound c 0 n W + accessBound c 0 n W

theorem formedAccessWork_bound {n W : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (address : Fin (n * W)) : formedAccessWork primitive address ≤ formedAccessBound c n W :=
  Nat.add_le_add (formationWork_bound primitive c hPrimitive address)
    (by simpa only [Nat.zero_add] using accessWork_bound primitive c hPrimitive 0 address)

end Blotto.FixedWordRegion

namespace Blotto.RationalTerminalPacking

def routeBitBuildWithFormedAddresses {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (W : ℕ) (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) : ℕ :=
  p.routeBitBuildWork primitive W hFit (FixedWordRegion.formedAccessWork primitive)

theorem routeBitBuildWithFormedAddresses_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c W : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) :
    p.routeBitBuildWithFormedAddresses primitive W hFit ≤ routeBitBuildBound c n s W (FixedWordRegion.formedAccessBound c n W) := by
  apply p.routeBitBuildWork_bound D s h hD hB hs hWidth primitive c W hPrimitive hFit
  exact FixedWordRegion.formedAccessWork_bound primitive c hPrimitive

end Blotto.RationalTerminalPacking

namespace Blotto.BinaryRouteSlot
open scoped BigOperators

def formationWork {n W : ℕ} (primitive : ℕ → ℕ) (j : Fin n) : ℕ :=
  ∑ offset : Fin W, FixedWordRegion.formationWork primitive (FixedWordRegion.localAddress j offset)

theorem formationWork_bound {n W : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (j : Fin n) :
    formationWork (W := W) primitive j ≤ W * BinaryAddressFormation.encodedWorkBound c 0 n W := by
  calc
    _ ≤ ∑ _offset : Fin W, BinaryAddressFormation.encodedWorkBound c 0 n W := Finset.sum_le_sum (fun offset _ =>
      FixedWordRegion.formationWork_bound primitive c hPrimitive (FixedWordRegion.localAddress j offset))
    _ = _ := by simp

end Blotto.BinaryRouteSlot
