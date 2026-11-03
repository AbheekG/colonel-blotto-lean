import Blotto.FixedWordRegion
import Blotto.RationalRouteBitBuildWork

/-! Bit-address validation/access prices use each actual address width.
The allocated region supplies a common word cap, without primitive monotonicity.
Address formation multiplication and allocation contracts are separate. -/

namespace Blotto.FixedWordRegion

def accessWork (primitive : ℕ → ℕ) (address : ℕ) : ℕ :=
  4 * binaryWordWidth (address + 1) + 2 * primitive (binaryWordWidth (address + 1)) + 6

def accessBound (c base n W : ℕ) : ℕ := (4 + 2 * c) * addressWidth base n W + 6

theorem accessWork_bound {n W : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (base : ℕ) (address : Fin (n * W)) : accessWork primitive (base + address.val) ≤ accessBound c base n W := by
  have hWidth := binaryWordWidth_mono (show base + address.val + 1 ≤ base + n * W + 1 by omega)
  have hp := (hPrimitive (binaryWordWidth (base + address.val + 1))).trans (Nat.mul_le_mul_left c hWidth)
  unfold accessWork accessBound addressWidth
  nlinarith

end Blotto.FixedWordRegion

namespace Blotto.RationalTerminalPacking

def routeBitBuildWithAccessWork {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (W : ℕ) (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) : ℕ :=
  p.routeBitBuildWork primitive W hFit (fun address => FixedWordRegion.accessWork primitive address.val)

theorem routeBitBuildWithAccessWork_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c W : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (hFit : ∀ e ∈ p.routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W) :
    p.routeBitBuildWithAccessWork primitive W hFit ≤
      routeBitBuildBound c n s W (FixedWordRegion.accessBound c 0 n W) := by
  apply p.routeBitBuildWork_bound D s h hD hB hs hWidth primitive c W hPrimitive hFit
  intro address
  simpa only [Nat.zero_add] using FixedWordRegion.accessWork_bound primitive c hPrimitive 0 address

end Blotto.RationalTerminalPacking
