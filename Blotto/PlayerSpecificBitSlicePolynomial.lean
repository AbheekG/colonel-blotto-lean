import Blotto.PlayerSpecificBitSliceCost

/-! Actual bit-slice source work is cubic in the encoded packet length,
uniformly including empty slices and boundary offsets. -/
namespace Blotto.PlayerSpecificBitSlicePolynomial
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 120*(192^2+192)
theorem width_bound (M : ℕ) : PlayerSpecificBitSliceCost.width M≤192*(M+1) := by
  unfold PlayerSpecificBitSliceCost.width PlayerSpecificResourceBlockReadCost.width PlayerSpecificResourceBlockReadCost.scale
  omega

theorem multiply_profile (K C R B M : ℕ) (h : C*R≤C*B*(M+1)^2) :
    C*(K+1)*R≤(K+1)*(C*B*(M+1)^2) := by
  have hp:=Nat.mul_le_mul_left (K+1) h
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hp

theorem cost (M offset K : ℕ) (h : offset+K≤M) (bits : Fin M → Bool) :
    (PlayerSpecificBitSliceExecution.run RationalCostModel.schoolbook M offset K h bits).2≤coefficient*(M+1)^3 := by
  have hc:=PlayerSpecificBitSliceCost.cost RationalCostModel.schoolbook M offset K h bits
  have hw:=RationalCostModel.schoolbook.monotone (width_bound M)
  have hc':=hc.trans (Nat.mul_le_mul_left (120*(K+1)) hw)
  have hq:=Blotto.PlayerSpecificAlgebraicInverseContract.quadratic_profile 120 192 (M+1) (by omega)
  have hmul:=multiply_profile K 120 (RationalCostModel.schoolbook.rat (192*(M+1))) (192^2+192) M hq
  have hK : K+1≤M+1 := by omega
  have hp:=Nat.mul_le_mul_right (coefficient*(M+1)^2) hK
  exact ((hc'.trans hmul).trans hp).trans_eq (by ring)

end Blotto.PlayerSpecificBitSlicePolynomial
