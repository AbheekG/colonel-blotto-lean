import Blotto.PlayerSpecificTerminalLeafMeasuredSourceCost
import Blotto.PlayerSpecificAlgebraicTerminalLeafPolynomial

/-! The measured original-coordinate leaf emitter has a fixed-degree
schoolbook bit-cost bound in the original row height, number of fields,
and scalar precision. This is a consequence of its actual source price. -/
namespace Blotto.PlayerSpecificTerminalLeafEmissionPolynomial
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (N T K : ℕ) : ℕ :=
  PlayerSpecificAlgebraicTerminalLeafBounds.height N T K+N+7

def coefficient : ℕ :=
  16000001000*PlayerSpecificResourceCostProfile.rationalCoefficient*
    (PlayerSpecificAlgebraicTerminalLeafPolynomial.coefficient+8)^3

theorem member_height_le (N T K : ℕ) :
    PlayerSpecificTerminalLeafMemberSourceCost.height N T K≤height N T K := by
  have h := PlayerSpecificAlgebraicExpressionBudget.fuel_mono
    (PlayerSpecificAlgebraicTerminalLeafBounds.base N T K) (show 1≤2 by decide)
  change step (PlayerSpecificAlgebraicTerminalLeafBounds.base N T K)≤
    PlayerSpecificAlgebraicTerminalLeafBounds.height N T K at h
  change step (PlayerSpecificAlgebraicTerminalLeafBounds.base N T K)+N+7≤
    PlayerSpecificAlgebraicTerminalLeafBounds.height N T K+N+7
  exact Nat.add_le_add_right (Nat.add_le_add_right h N) 7

theorem frame_height_le (N T K : ℕ) :
    PlayerSpecificTerminalLeafEmissionSourceCost.frameHeight N T K≤height N T K := by
  change max (PlayerSpecificAlgebraicTerminalLeafBounds.height N T K) N+6≤
    PlayerSpecificAlgebraicTerminalLeafBounds.height N T K+N+7
  omega

theorem height_linear (N T K : ℕ) :
    PlayerSpecificAlgebraicTerminalLeafBounds.height N T K+N+7+1≤
      (PlayerSpecificAlgebraicTerminalLeafPolynomial.coefficient+8)*(N+1)*(T+K+1) := by
  let V:=(N+1)*(T+K+1)
  have hleaf := PlayerSpecificAlgebraicTerminalLeafPolynomial.height_bound N T K
  have hV : N+1≤V := by
    dsimp only [V]
    exact Nat.le_mul_of_pos_right (N+1) (by omega : 0<T+K+1)
  have hNV : N+7≤8*V := by
    have h := Nat.mul_le_mul_left 8 hV
    omega
  have hleaf' : PlayerSpecificAlgebraicTerminalLeafBounds.height N T K+1≤
      PlayerSpecificAlgebraicTerminalLeafPolynomial.coefficient*V := by
    simpa only [V,mul_assoc] using hleaf
  have hassoc : PlayerSpecificAlgebraicTerminalLeafBounds.height N T K+N+7+1 =
      (PlayerSpecificAlgebraicTerminalLeafBounds.height N T K+1)+(N+7) := by omega
  have hsum := Nat.add_le_add hleaf' hNV
  have heq : PlayerSpecificAlgebraicTerminalLeafPolynomial.coefficient*V+8*V =
      (PlayerSpecificAlgebraicTerminalLeafPolynomial.coefficient+8)*V := by ring
  have hresult : PlayerSpecificAlgebraicTerminalLeafBounds.height N T K+N+7+1≤
      (PlayerSpecificAlgebraicTerminalLeafPolynomial.coefficient+8)*V := by
    rw [hassoc]
    exact hsum.trans_eq heq
  simpa only [V,mul_assoc] using hresult

theorem work_polynomial (N T K : ℕ) :
    PlayerSpecificTerminalLeafEmissionSourceCost.work N T K≤
      coefficient*(N+1)^4*(T+K+1)^3 := by
  let model:=Blotto.RationalCostModel.schoolbook
  let Z:=height N T K
  let R:=model.rat (PlayerSpecificAlgebraicComparisonExecution.width Z)
  have hm := model.monotone (PlayerSpecificSegmentSelectionSizes.width_mono (member_height_le N T K))
  have hf := model.monotone (PlayerSpecificSegmentSelectionSizes.width_mono (frame_height_le N T K))
  have hc : N*16000000009+(200*(N+N+1)+9)≤16000001000*(N+1) := by omega
  have hcost : PlayerSpecificTerminalLeafEmissionSourceCost.work N T K≤
      (16000001000*(N+1))*R := by
    rw [PlayerSpecificTerminalLeafEmissionSourceCost.work,
      PlayerSpecificTerminalLeafMemberSourceCost.work]
    have ha := Nat.mul_le_mul_left N (Nat.mul_le_mul_left 16000000009 hm)
    have hb := Nat.mul_le_mul_left (200*(N+N+1)+9) hf
    have hboth := Nat.add_le_add ha hb
    have hshape : N*(16000000009*R)+(200*(N+N+1)+9)*R =
        (N*16000000009+(200*(N+N+1)+9))*R := by ring
    exact (hboth.trans_eq hshape).trans (Nat.mul_le_mul_right R hc)
  have hrat := PlayerSpecificSegmentSelectionSizes.rational_polynomial
    (16000001000*(N+1)) Z
  have hZ : Z+1≤
      (PlayerSpecificAlgebraicTerminalLeafPolynomial.coefficient+8)*(N+1)*(T+K+1) :=
    height_linear N T K
  have hpow := Nat.pow_le_pow_left hZ 3
  have hscaled := Nat.mul_le_mul_left
    ((16000001000*(N+1))*PlayerSpecificResourceCostProfile.rationalCoefficient) hpow
  calc
    _ ≤ (16000001000*(N+1))*R := hcost
    _ ≤ ((16000001000*(N+1))*PlayerSpecificResourceCostProfile.rationalCoefficient)*(Z+1)^3 := hrat
    _ ≤ ((16000001000*(N+1))*PlayerSpecificResourceCostProfile.rationalCoefficient)*
      ((PlayerSpecificAlgebraicTerminalLeafPolynomial.coefficient+8)*(N+1)*(T+K+1))^3 := hscaled
    _ = coefficient*(N+1)^4*(T+K+1)^3 := by
      dsimp only [coefficient]
      ring

end Blotto.PlayerSpecificTerminalLeafEmissionPolynomial
