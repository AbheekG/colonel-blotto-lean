import Blotto.PlayerSpecificNestedPacketSourceCost

/-! The two-level eighteen-slot nested packet has linear address width and
cubic bit-copy work in the two caller precisions. -/
namespace Blotto.PlayerSpecificNestedPacketSourcePolynomial
set_option autoImplicit false

theorem size_bound (H K : ℕ) :
    PlayerSpecificNestedPacketSourceCost.size 18 H K + 1 ≤ 29*(H+K+1) := by
  unfold PlayerSpecificNestedPacketSourceCost.size
  omega

theorem work_bound (H K : ℕ) :
    PlayerSpecificNestedPacketSourceCost.coefficient *
      (PlayerSpecificNestedPacketSourceCost.size 18 H K+1)^3 ≤
    (PlayerSpecificNestedPacketSourceCost.coefficient*29^3)*(H+K+1)^3 := by
  have h := Nat.pow_le_pow_left (size_bound H K) 3
  have h' := Nat.mul_le_mul_left PlayerSpecificNestedPacketSourceCost.coefficient h
  exact h'.trans_eq (by ring)

end Blotto.PlayerSpecificNestedPacketSourcePolynomial
