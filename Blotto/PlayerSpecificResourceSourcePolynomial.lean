import Blotto.PlayerSpecificOriginalResourceSourceCost

/-! The aggregate resource-loop bound is polynomial in the original
input dimension/bit length and Bernoulli precision. -/
namespace Blotto.PlayerSpecificResourceSourcePolynomial
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem size_bound (N L H : ℕ) : PlayerSpecificOriginalResourceSourceCost.size N L H+1≤
    (PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)*(N+1)^2*(L+H+1) := by
  let Q:=(N+1)^2*(L+H+1)
  have hb:=PlayerSpecificAlgebraicFiniteDrawHeights.base_bound N L H
  have hsquare : N+1≤(N+1)^2 := by nlinarith only [Nat.zero_le N,Nat.zero_le (N*N)]
  have hQ : N+1≤Q := by
    have hm:=Nat.mul_le_mul_left ((N+1)^2) (show 1≤L+H+1 by omega)
    simp only [Nat.mul_one] at hm
    exact hsquare.trans hm
  unfold PlayerSpecificOriginalResourceSourceCost.size
  dsimp only [Q] at hQ
  nlinarith only [hb,hQ]

theorem transfer (C D E N A U V : ℕ) (hU : U+1≤D*(N+1)^2*A) (hV : V+1≤E*(U+1)) :
    (N+1)*C*(V+1)^3≤(C*(E*D)^3)*(N+1)^7*A^3 := by
  have hv: V+1≤(E*D)*(N+1)^2*A := hV.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left E hU)
  have hp:=Nat.mul_le_mul_left ((N+1)*C) (Nat.pow_le_pow_left hv 3)
  exact hp.trans_eq (by ring)

def coefficient : ℕ := PlayerSpecificFiniteResourceSourceCost.coefficient*
  ((8*PlayerSpecificAlgebraicHeightEnvelope.coefficient+107)*(PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1))^3

theorem work_bound (N L H : ℕ) : PlayerSpecificOriginalResourceSourceCost.work N L H≤
    coefficient*(N+1)^7*(L+H+1)^3 :=
  transfer PlayerSpecificFiniteResourceSourceCost.coefficient (PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)
    (8*PlayerSpecificAlgebraicHeightEnvelope.coefficient+107) N (L+H+1)
      (PlayerSpecificOriginalResourceSourceCost.size N L H)
      (PlayerSpecificResourceStepSizes.height (PlayerSpecificOriginalResourceSourceCost.size N L H))
      (size_bound N L H) (PlayerSpecificResourceStepSizes.linear _)

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∀ (player : Bool) (H : ℕ) (bits : Fin ((N-1)*H) → Bool),
      (PlayerSpecificFiniteResourceExecution.run RationalCostModel.schoolbook p H (N-1)
        (PlayerSpecificAlgebraicResourceState.start RationalCostModel.schoolbook p player)
        (PlayerSpecificFiniteResourceLoop.blocks (N-1) H bits)).2≤
          coefficient*(N+1)^7*(PlayerSpecificInitialPositivePrecision.inputSize i+H+1)^3 := by
  dsimp only
  intro player H bits
  exact (PlayerSpecificOriginalResourceSourceCost.original_input i r hr player H bits).trans (work_bound N _ H)

end Blotto.PlayerSpecificResourceSourcePolynomial
