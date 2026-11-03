import Blotto.PlayerSpecificSegmentSelectionFrameCost

/-! Derived shared sizes and polynomial backend calibration for actual
segment-choice steps. Coin precision enters only the analyzed size. -/
namespace Blotto.PlayerSpecificSegmentSelectionSizes
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def size (S H slots : ℕ) : ℕ := PlayerSpecificAlgebraicHeightEnvelope.step S+H+slots+10
def nodeCoefficient : ℕ := 8200001000*PlayerSpecificResourceCostProfile.rationalCoefficient+
  PlayerSpecificAlgebraicCoinCost.polynomialCoefficient
def work (S H slots : ℕ) : ℕ := nodeCoefficient*(slots+1)*(size S H slots+1)^3

theorem lower (S H slots : ℕ) : S≤size S H slots ∧ PlayerSpecificAlgebraicHeightEnvelope.step S≤size S H slots ∧
    H≤size S H slots ∧ slots≤size S H slots ∧ 1≤size S H slots := by
  have hl:=PlayerSpecificAlgebraicHeightEnvelope.large S
  dsimp [size]
  omega

theorem width_mono {S U : ℕ} (h : S≤U) : PlayerSpecificAlgebraicComparisonExecution.width S≤PlayerSpecificAlgebraicComparisonExecution.width U := by
  rw [PlayerSpecificAlgebraicComparisonCost.width_linear,PlayerSpecificAlgebraicComparisonCost.width_linear]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1)

theorem rational_polynomial (C U : ℕ) : C*RationalCostModel.schoolbook.rat (PlayerSpecificAlgebraicComparisonExecution.width U)≤
    (C*PlayerSpecificResourceCostProfile.rationalCoefficient)*(U+1)^3 := by
  have hC : C≤C*(U+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left C (show 1≤U+1 by omega)
  exact (Nat.mul_le_mul_right _ hC).trans (PlayerSpecificResourceCostProfile.cubic C U)

theorem node_profile (R Q M X : ℕ) :
    (8000000000*R)*X+Q*X+(200000000*R)*X+((1000*(M+1))*R)*X≤
      (8200001000*R+Q)*(M+1)*X := by
  nlinarith only [Nat.zero_le (M*R*X),Nat.zero_le (M*Q*X)]

theorem frame_profile (R Q M X : ℕ) : ((1000*(M+1))*R)*X≤(8200001000*R+Q)*(M+1)*X := by
  nlinarith only [Nat.zero_le (R*X),Nat.zero_le (M*R*X),Nat.zero_le (Q*(M+1)*X)]

theorem accepted_profile (R Q M X : ℕ) :
    (8000000000*R)*X+Q*X+((1000*(M+1))*R)*X≤(8200001000*R+Q)*(M+1)*X := by
  nlinarith only [node_profile R Q M X,Nat.zero_le (R*X)]

theorem size_linear (S H slots : ℕ) : size S H slots+1≤
    (PlayerSpecificAlgebraicHeightEnvelope.coefficient+12)*(S+H+slots+1) := by
  dsimp [size,PlayerSpecificAlgebraicHeightEnvelope.step]
  nlinarith only [Nat.zero_le (PlayerSpecificAlgebraicHeightEnvelope.coefficient*H),
    Nat.zero_le (PlayerSpecificAlgebraicHeightEnvelope.coefficient*slots),Nat.zero_le S,Nat.zero_le H,Nat.zero_le slots]

end Blotto.PlayerSpecificSegmentSelectionSizes
