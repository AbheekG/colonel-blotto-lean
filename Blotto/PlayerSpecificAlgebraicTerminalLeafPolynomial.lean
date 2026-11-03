import Blotto.PlayerSpecificAlgebraicFiniteDrawContract

/-! The actual terminal output height is linear in reached stored-row
height and scalar precision, with only one additional factor in the
number of original coordinates. All constants are absolute. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalLeafPolynomial
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem group_profile (N T K : ℕ) :
    ((T+1)*(N+N)+3)+T+1+1 ≤ 6*(N+1)*(T+K+1) := by
  nlinarith only [Nat.zero_le N,Nat.zero_le T,Nat.zero_le K,Nat.zero_le (N*T),Nat.zero_le (N*K)]

theorem preparation_profile (C N T K : ℕ) :
    C*(((T+1)*(N+N)+3)+T+1+1)+K+1 ≤ (6*C+1)*(N+1)*(T+K+1) := by
  have hg := Nat.mul_le_mul_left C (group_profile N T K)
  have hk : K+1 ≤ (N+1)*(T+K+1) := by
    nlinarith only [Nat.zero_le T,Nat.zero_le (N*(T+K+1))]
  nlinarith only [hg,hk]

def coefficient : ℕ := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^2*
  (PlayerSpecificAlgebraicTerminalCoreDrawBounds.coefficient*(6*PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)+6)

theorem height_bound (N T K : ℕ) : PlayerSpecificAlgebraicTerminalLeafBounds.height N T K+1 ≤
    coefficient*(N+1)*(T+K+1) := by
  have hp : PlayerSpecificAlgebraicTerminalCorePreparationSizes.height N T+K+1 ≤
      (6*PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)*(N+1)*(T+K+1) :=
    preparation_profile PlayerSpecificAlgebraicHeightEnvelope.coefficient N T K
  have hc := (PlayerSpecificAlgebraicTerminalCoreDrawBounds.height_linear
    (PlayerSpecificAlgebraicTerminalCorePreparationSizes.height N T) K).trans
      (Nat.mul_le_mul_left PlayerSpecificAlgebraicTerminalCoreDrawBounds.coefficient hp)
  change PlayerSpecificAlgebraicTerminalCoreExecution.height N T K+1 ≤ _ at hc
  have hg := group_profile N T K
  have hb : PlayerSpecificAlgebraicTerminalLeafBounds.base N T K+1 ≤
      (PlayerSpecificAlgebraicTerminalCoreDrawBounds.coefficient*(6*PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)+6)*
        (N+1)*(T+K+1) := by
    dsimp only [PlayerSpecificAlgebraicTerminalLeafBounds.base]
    nlinarith only [hc,hg]
  have hi := (iterate_bound 2 (PlayerSpecificAlgebraicTerminalLeafBounds.base N T K)).trans
    (Nat.mul_le_mul_left ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^2) hb)
  simpa only [PlayerSpecificAlgebraicTerminalLeafBounds.height,coefficient,mul_assoc] using hi

end Blotto.PlayerSpecificAlgebraicTerminalLeafPolynomial
