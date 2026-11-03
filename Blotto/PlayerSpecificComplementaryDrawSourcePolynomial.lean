import Blotto.PlayerSpecificComplementaryDrawSourceCost

/-! A fixed cubic envelope for the actual complementary two-group
source work, including midpoint decoding and returned rows. -/
namespace Blotto.PlayerSpecificComplementaryDrawSourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private def A : ℕ := PlayerSpecificAlgebraicHeightEnvelope.coefficient+1
private def E : ℕ := A^3
private def R : ℕ := PlayerSpecificResourceCostProfile.rationalCoefficient

def coefficient : ℕ :=
  2000*(192*192+192)+
  (8000000000*R)*(1+A^3+E^3)+
  (1200*R)*(E+4)^3+2

theorem work_bound (T K : ℕ) :
    PlayerSpecificComplementaryDrawSourceCost.work T K≤
      coefficient*(T+K+5)^3 := by
  let X:=T+K+5
  have hX : 1≤X := by dsimp only [X]; omega
  have hK : K+1≤X := by dsimp only [X]; omega
  have hTK : T+K+4≤X := by dsimp only [X]; omega
  have hstep0:=PlayerSpecificAlgebraicHeightEnvelope.iterate_bound 1 (T+K+3)
  have hstep : PlayerSpecificAlgebraicHeightEnvelope.step (T+K+3)+1≤A*X := by
    have hb : T+K+3+1≤X := by dsimp only [X]; omega
    have hm:=Nat.mul_le_mul_left A hb
    simpa only [PlayerSpecificAlgebraicHeightEnvelope.iterate,pow_one,A] using
      hstep0.trans hm
  have hheight0:=PlayerSpecificAlgebraicHeightEnvelope.iterate_bound 3 (T+K+3)
  have hheight : PlayerSpecificAlgebraicComplementaryDraw.height T K+1≤E*X := by
    have hb : T+K+3+1≤X := by dsimp only [X]; omega
    have hm:=Nat.mul_le_mul_left E hb
    simpa only [PlayerSpecificAlgebraicComplementaryDraw.height,E,A] using
      hheight0.trans hm
  have hheight5 : PlayerSpecificAlgebraicComplementaryDraw.height T K+5≤
      (E+4)*X := by
    have hfour : 4≤4*X := by omega
    have h:=Nat.add_le_add hheight hfour
    convert h using 1; ring
  have hpK:=Nat.pow_le_pow_left hK 3
  have hpTK:=Nat.pow_le_pow_left hTK 3
  have hpS:=Nat.pow_le_pow_left hstep 3
  have hpH:=Nat.pow_le_pow_left hheight 3
  have hpH5:=Nat.pow_le_pow_left hheight5 3
  have h1 : (K+1)^3≤X^3 := hpK
  have h2 : (T+K+4)^3≤X^3 := hpTK
  have h3 : (PlayerSpecificAlgebraicHeightEnvelope.step (T+K+3)+1)^3≤A^3*X^3 := by
    convert hpS using 1; ring
  have h4 : (PlayerSpecificAlgebraicComplementaryDraw.height T K+1)^3≤E^3*X^3 := by
    convert hpH using 1; ring
  have h5 : (PlayerSpecificAlgebraicComplementaryDraw.height T K+5)^3≤(E+4)^3*X^3 := by
    convert hpH5 using 1; ring
  have hsmall : 2≤2*X^3 := by
    have hp : 1≤X^3 := by simpa only [one_pow] using Nat.pow_le_pow_left hX 3
    omega
  have hsum:=Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.mul_le_mul_left (2000*(192*192+192)) h1)
          (Nat.mul_le_mul_left (8000000000*R) h2))
        (Nat.mul_le_mul_left (8000000000*R) h3))
      (Nat.mul_le_mul_left (8000000000*R) h4))
    (Nat.add_le_add (Nat.mul_le_mul_left (1200*R) h5) hsmall)
  have hwork : PlayerSpecificComplementaryDrawSourceCost.work T K≤
      2000*(192*192+192)*X^3+
      (8000000000*R)*X^3+
      (8000000000*R)*(A^3*X^3)+
      (8000000000*R)*(E^3*X^3)+
      ((1200*R)*((E+4)^3*X^3)+2*X^3) := by
    simp only [PlayerSpecificComplementaryDrawSourceCost.work,Nat.add_assoc]
    dsimp only [R] at hsum ⊢
    simpa only [Nat.add_assoc] using hsum
  calc
    PlayerSpecificComplementaryDrawSourceCost.work T K ≤ _ := hwork
    _ = coefficient*X^3 := by simp only [coefficient]; ring

end Blotto.PlayerSpecificComplementaryDrawSourcePolynomial
