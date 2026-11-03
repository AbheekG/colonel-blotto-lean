import Blotto.PlayerSpecificAlgebraicTerminalLeafPolynomial

/-! The complete actual finite-bit field-valued draw has one polynomial
coefficient bound in the original input and scalar precision. The proof
uses reached lineages and direct leaves, never recursive product depth. -/
namespace Blotto.PlayerSpecificAlgebraicFiniteDrawHeights
open PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicFiniteDraw
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem base_profile (CF CI CR N L K F I : ℕ)
    (hF : F ≤ CF*(N+1)*(L+1)) (hI : I ≤ CI*(N+1)*(L+1)) :
    F+I+3*(CR*(N+1)^2*(L+1)+1)+L+2+K+1 ≤
      (CF+CI+3*CR+7)*(N+1)^2*(L+K+1) := by
  let Q := (N+1)^2*(L+K+1)
  have hsq : N+1 ≤ (N+1)^2 := by nlinarith only [Nat.zero_le N,Nat.zero_le (N*N)]
  have hl : (N+1)*(L+1) ≤ Q := Nat.mul_le_mul hsq (by omega)
  have hFQ : F ≤ CF*Q := hF.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left CF hl)
  have hIQ : I ≤ CI*Q := hI.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left CI hl)
  have hPQ : (N+1)^2*(L+1) ≤ Q := Nat.mul_le_mul_left ((N+1)^2) (by omega)
  have hRQ := Nat.mul_le_mul_left (3*CR) hPQ
  have hLQ : L+K+1 ≤ Q := by
    have h1 : 1 ≤ (N+1)^2 := by nlinarith only [Nat.zero_le N,Nat.zero_le (N*N)]
    simpa only [one_mul] using Nat.mul_le_mul_right (L+K+1) h1
  have hsmall : L+K+6 ≤ 7*Q := by omega
  dsimp only [Q] at hFQ hIQ hRQ hsmall
  nlinarith only [hFQ,hIQ,hRQ,hsmall]

def baseCoefficient : ℕ := 11*PlayerSpecificFiniteScaleHeights.coefficient+
  PlayerSpecificInitialPositivePrecision.initialCoefficient+3*PlayerSpecificInitialLineageBound.coefficient+7
def coefficient : ℕ := PlayerSpecificAlgebraicTerminalLeafPolynomial.coefficient*baseCoefficient

theorem base_bound (N L K : ℕ) : PlayerSpecificAlgebraicFiniteDrawContract.base N L+K+1 ≤
    baseCoefficient*(N+1)^2*(L+K+1) := by
  have h := base_profile (11*PlayerSpecificFiniteScaleHeights.coefficient)
    PlayerSpecificInitialPositivePrecision.initialCoefficient PlayerSpecificInitialLineageBound.coefficient N L K
    (PlayerSpecificFiniteParameterSizes.height N L) (PlayerSpecificAlgebraicInitialInputSizes.height N L)
    (PlayerSpecificFiniteParameterSizes.polynomial_height N L) (PlayerSpecificAlgebraicInitialInputSizes.polynomial_height N L)
  simpa only [PlayerSpecificAlgebraicFiniteDrawContract.base,PlayerSpecificAlgebraicPathContract.height,
    PlayerSpecificInitialLineageBound.height,baseCoefficient] using h

theorem polynomial_height (N L K : ℕ) : PlayerSpecificAlgebraicFiniteDrawContract.height N L K+1 ≤
    coefficient*(N+1)^3*(L+K+1) := by
  have h := (PlayerSpecificAlgebraicTerminalLeafPolynomial.height_bound N (PlayerSpecificAlgebraicFiniteDrawContract.base N L) K).trans
    (Nat.mul_le_mul_left (PlayerSpecificAlgebraicTerminalLeafPolynomial.coefficient*(N+1)) (base_bound N L K))
  calc
    _ ≤ _ := h
    _ = coefficient*(N+1)^3*(L+K+1) := by simp only [coefficient,pow_succ,pow_zero]; ring

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p := PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      ∀ (player : Bool) (H K : ℕ) (bits : Fin (bitCount N H K) → Bool),
        FullBudget (if player then 1 else (i.budget:ℝ)) (PlayerSpecificAlgebraicSegment.values (draw p i.budget player H K bits) x) ∧
          ∀ j,PlayerSpecificAlgebraicReduction.Reduced r.root.polynomial ((draw p i.budget player H K bits).read j) ∧
            HasHeight ((draw p i.budget player H K bits).read j)
              (coefficient*(N+1)^3*(PlayerSpecificInitialPositivePrecision.inputSize i+K+1)) := by
  obtain ⟨x,hx,hdraw⟩ := PlayerSpecificAlgebraicFiniteDrawContract.original_input i r hr
  refine ⟨x,hx,?_⟩
  intro player H K bits
  have h := hdraw player H K bits
  refine ⟨h.1,?_⟩
  intro j
  exact ⟨(h.2 j).1,PlayerSpecificPolynomialHeights.mono (h.2 j).2
    ((Nat.le_succ _).trans (polynomial_height N (PlayerSpecificInitialPositivePrecision.inputSize i) K))⟩

end Blotto.PlayerSpecificAlgebraicFiniteDrawHeights
