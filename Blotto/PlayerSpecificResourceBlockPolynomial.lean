import Blotto.PlayerSpecificResourceBlockCost

/-! Complete measured fair-block construction is polynomial in the
number of blocks and their precision, including offset arithmetic. -/
namespace Blotto.PlayerSpecificResourceBlockPolynomial
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem width_bound (fuel H : ℕ) : PlayerSpecificResourceBlockReadCost.width fuel H≤192*((fuel+1)*(H+1)) := by
  unfold PlayerSpecificResourceBlockReadCost.width PlayerSpecificResourceBlockReadCost.scale
  nlinarith only [Nat.zero_le (fuel*H),Nat.zero_le fuel,Nat.zero_le H]

def coefficient : ℕ := 300*(192*192+192)

theorem cost (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) :
    (PlayerSpecificResourceBlockExecution.blocks RationalCostModel.schoolbook fuel H bits).2≤
      coefficient*(fuel+1)^3*(H+1)^3 := by
  have hc:=PlayerSpecificResourceBlockCost.cost RationalCostModel.schoolbook fuel H bits
  have hwidth:=RationalCostModel.schoolbook.monotone (width_bound fuel H)
  have hp:=hc.trans (Nat.mul_le_mul_left (300*(fuel+1)*(H+1)) hwidth)
  have hq : 1≤(fuel+1)*(H+1) := Nat.mul_pos (by omega) (by omega)
  have hprofile:=PlayerSpecificAlgebraicPairCost.cubic_profile 300 192 ((fuel+1)*(H+1)) hq
  have he : 300*(fuel+1)*(H+1)=300*((fuel+1)*(H+1)) := by ring
  rw [he] at hp
  exact (hp.trans hprofile).trans_eq (by unfold coefficient; ring)

end Blotto.PlayerSpecificResourceBlockPolynomial
