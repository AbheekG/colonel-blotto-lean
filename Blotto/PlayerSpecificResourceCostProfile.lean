import Blotto.PlayerSpecificResourceLoopFrameCost

/-! Shared cubic calibration for already measured resource callers.
The coefficient is fixed and no analysis width enters runtime execution. -/
namespace Blotto.PlayerSpecificResourceCostProfile
set_option autoImplicit false
set_option maxHeartbeats 2500000

def rationalCoefficient : ℕ := PlayerSpecificAlgebraicComparisonCost.widthCoefficient^2+
  PlayerSpecificAlgebraicComparisonCost.widthCoefficient

theorem cubic (C S : ℕ) :
    C*(S+1)*RationalCostModel.schoolbook.rat (PlayerSpecificAlgebraicComparisonExecution.width S)≤
      C*rationalCoefficient*(S+1)^3 := by
  rw [PlayerSpecificAlgebraicComparisonCost.width_linear]
  exact PlayerSpecificAlgebraicPairCost.cubic_profile C _ _ (by omega)

theorem request_profile (S : ℕ) :
    PlayerSpecificAlgebraicPairCost.polynomialCoefficient*(S+1)^3+
      150*(3*S+1)*RationalCostModel.schoolbook.rat (PlayerSpecificAlgebraicComparisonExecution.width S)≤
        (PlayerSpecificAlgebraicPairCost.polynomialCoefficient+450*rationalCoefficient)*(S+1)^3 := by
  have hc:=cubic 450 S
  have hm:=Nat.mul_le_mul_right (RationalCostModel.schoolbook.rat (PlayerSpecificAlgebraicComparisonExecution.width S))
    (show 150*(3*S+1)≤450*(S+1) by omega)
  have ht:=Nat.add_le_add_left (hm.trans hc) (PlayerSpecificAlgebraicPairCost.polynomialCoefficient*(S+1)^3)
  exact ht.trans_eq (by ring)

end Blotto.PlayerSpecificResourceCostProfile
