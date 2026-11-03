import Blotto.PlayerSpecificSelectedRefinement

/-! The selected interval supplies its own computed integer enclosure,
derived from the actual encoded rational endpoints. -/
namespace Blotto.PlayerSpecificSignEnclosure
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 1000000

def endpointHeight (node : Interval) : ℕ := inputHeight [node.lo,node.hi]
def magnitude (node : Interval) : ℕ := 2^endpointHeight node

theorem positive (node : Interval) : 0<magnitude node := Nat.two_pow_pos _

theorem endpoints (node : Interval) : |(node.lo:ℝ)| < (magnitude node:ℝ) ∧ |(node.hi:ℝ)| < (magnitude node:ℝ) := by
  have hlo:=real_upper node.lo (endpointHeight node) (member_height [node.lo,node.hi] node.lo (by simp))
  have hhi:=real_upper node.hi (endpointHeight node) (member_height [node.lo,node.hi] node.hi (by simp))
  simpa only [magnitude,Nat.cast_pow,Nat.cast_ofNat] using And.intro hlo hhi

theorem inside_bound (node : Interval) (x : ℝ) (hx : node.Contains x) : |x| ≤ (magnitude node:ℝ) := by
  have he:=endpoints node
  have hl:=abs_lt.mp he.1
  have hh:=abs_lt.mp he.2
  exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem width_bound (node : Interval) : (node.width:ℝ)≤2*(magnitude node:ℝ) := by
  have he:=endpoints node
  have hl:=abs_lt.mp he.1
  have hh:=abs_lt.mp he.2
  change ((node.hi-node.lo:ℚ):ℝ)≤_
  rw [Rat.cast_sub]
  linarith

def retag {p : Data} (prepared : Prepared p) (node : Interval) : Interval := initial prepared node.lo node.hi

theorem initial_valid {p : Data} (prepared : Prepared p) (node : Interval) (hv : node.lo<node.hi) :
    Valid prepared (retag prepared node) := PlayerSpecificIsolationState.initial_valid prepared _ _ hv

theorem initial_contains {p : Data} (prepared : Prepared p) (node : Interval) (x : ℝ) :
    (retag prepared node).Contains x ↔ node.Contains x := Iff.rfl

theorem initial_unique {p : Data} (prepared : Prepared p) (node : Interval) (x : ℝ)
    (hu : PlayerSpecificSelectedRefinement.Unique p node x) :
    PlayerSpecificSelectedRefinement.Unique p (retag prepared node) x := hu

end Blotto.PlayerSpecificSignEnclosure
