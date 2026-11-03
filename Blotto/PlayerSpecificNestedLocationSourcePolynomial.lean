import Blotto.PlayerSpecificNestedLocationSourceCost

/-! A cubic source bound for midpoint location and its algebraic scalar. -/
namespace Blotto.PlayerSpecificNestedLocationSourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private def A : ℕ := PlayerSpecificAlgebraicHeightEnvelope.coefficient+1
private def R : ℕ := PlayerSpecificResourceCostProfile.rationalCoefficient

def coefficient : ℕ :=
  2000*(192*192+192)+8000000000*R+
  PlayerSpecificNestedParameterSourceCost.scalarCoefficient*(A+18)^3+2

theorem work_bound (H K : ℕ) :
    PlayerSpecificNestedLocationSourceCost.work H K ≤ coefficient*(H+K+5)^3 := by
  let X := H+K+5
  have hX : 1≤X := by dsimp [X]; omega
  have hK : K+1≤X := by dsimp [X]; omega
  have hHK : H+K+4≤X := by dsimp [X]; omega
  have hstep0:=PlayerSpecificAlgebraicHeightEnvelope.iterate_bound 1 (H+K+3)
  have hstep : PlayerSpecificAlgebraicHeightEnvelope.step (H+K+3)+1≤A*X := by
    have hb : H+K+3+1≤X := by dsimp [X]; omega
    have hm:=Nat.mul_le_mul_left A hb
    simpa only [PlayerSpecificAlgebraicHeightEnvelope.iterate,pow_one,A] using hstep0.trans hm
  have hlong : PlayerSpecificAlgebraicHeightEnvelope.step (H+K+3)+19≤(A+18)*X := by
    have h18 : 18≤18*X := by omega
    have h:=Nat.add_le_add hstep h18
    convert h using 1; ring
  have hpK:=Nat.pow_le_pow_left hK 3
  have hpHK:=Nat.pow_le_pow_left hHK 3
  have hpLong:=Nat.pow_le_pow_left hlong 3
  have hsmall : 2≤2*X^3 := by
    have hp : 1≤X^3 := by simpa only [one_pow] using Nat.pow_le_pow_left hX 3
    omega
  have hsum:=Nat.add_le_add
    (Nat.add_le_add
      (Nat.mul_le_mul_left (2000*(192*192+192)) hpK)
      (Nat.mul_le_mul_left (8000000000*R) hpHK))
    (Nat.add_le_add
      (Nat.mul_le_mul_left PlayerSpecificNestedParameterSourceCost.scalarCoefficient hpLong)
      hsmall)
  have hwork : PlayerSpecificNestedLocationSourceCost.work H K≤
      2000*(192*192+192)*X^3+
      (8000000000*R)*X^3+
      (PlayerSpecificNestedParameterSourceCost.scalarCoefficient*((A+18)*X)^3+2*X^3) := by
    change 2000*(192*192+192)*(K+1)^3+
      (8000000000*R)*(H+K+4)^3+
      PlayerSpecificNestedParameterSourceCost.scalarCoefficient*
        (PlayerSpecificAlgebraicHeightEnvelope.step (H+K+3)+19)^3+2≤_
    simpa only [Nat.add_assoc] using hsum
  calc
    PlayerSpecificNestedLocationSourceCost.work H K ≤ _ := hwork
    _ = coefficient*X^3 := by simp only [coefficient]; ring

end Blotto.PlayerSpecificNestedLocationSourcePolynomial
