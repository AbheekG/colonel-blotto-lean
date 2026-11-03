import Blotto.PlayerSpecificAlgebraicExpressionSourceCost

/-! Fixed local expression depth gives a complete polynomial source
price from actual input heights. All node envelopes are derived here;
no executing input supplies a height, sign, arithmetic or cost oracle. -/
namespace Blotto.PlayerSpecificAlgebraicExpressionFixedCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def size (H k D : ℕ) : ℕ := PlayerSpecificAlgebraicHeightEnvelope.iterate (D+1) (H+k+10)

theorem lower (H k D : ℕ) : H≤size H k D ∧ k≤size H k D ∧ 10≤size H k D := by
  have h:=PlayerSpecificAlgebraicExpressionBudget.initial_le (D+1) (H+k+10)
  unfold size
  omega

theorem input_cost {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (e : RationalExpression k) (H D : ℕ) (hDepth : e.depth≤D)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) (hLit : e.LiteralHeights H) :
    (PlayerSpecificAlgebraicExpressionExecution.run model root env e).2≤
      e.operationBound*PlayerSpecificAlgebraicExpressionPrimitiveCost.work model (size H k D) := by
  let U:=H+k+10
  let S:=size H k D
  have hHU : H≤U := by dsimp [U]; omega
  have hHnodes:=PlayerSpecificAlgebraicExpressionNodes.heights model root env e hm hm0 hml U D (mono hmH hHU) (by dsimp [U]; omega)
    (fun j => ⟨(hEnv j).1,mono (hEnv j).2 hHU⟩) (e.LiteralHeights_mono hHU hLit) hDepth
  have hHS : H≤S := (lower H k D).1
  exact PlayerSpecificAlgebraicExpressionSourceCost.cost model root env e S (lower H k D).2.1 (lower H k D).2.2
    hm hm0 hml (mono hmH hHS) (mono he hHS) hv (fun j => (hEnv j).1) (e.LiteralHeights_mono hHS hLit) hHnodes

theorem size_linear (H k D : ℕ) : size H k D+1≤
    (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^(D+1)*(H+k+11) := by
  simpa only [size,show H+k+10+1=H+k+11 by omega] using
    PlayerSpecificAlgebraicHeightEnvelope.iterate_bound (D+1) (H+k+10)

theorem calibrate (n C S R D : ℕ) (h : C*(S+1)*R≤C*D*(S+1)^3) :
    n*(C*(S+1)*R)≤n*(C*D)*(S+1)^3 := by
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left n h

theorem transfer (n C B X S : ℕ) (hS : S+1≤B*X) :
    n*C*(S+1)^3≤n*(C*B^3)*X^3 := by
  have hp:=Nat.mul_le_mul_left (n*C) (Nat.pow_le_pow_left hS 3)
  exact hp.trans_eq (by ring)

def polynomialCoefficient (D : ℕ) : ℕ := PlayerSpecificAlgebraicExpressionPrimitiveCost.coefficient*
  PlayerSpecificResourceCostProfile.rationalCoefficient*((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^(D+1))^3

theorem polynomial_cost {k : ℕ} (root : Candidate) (env : FixedArrayTable k Data) (e : RationalExpression k)
    (H D : ℕ) (hDepth : e.depth≤D)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) (hLit : e.LiteralHeights H) :
    (PlayerSpecificAlgebraicExpressionExecution.run RationalCostModel.schoolbook root env e).2≤
      e.operationBound*polynomialCoefficient D*(H+k+11)^3 := by
  have hc:=input_cost RationalCostModel.schoolbook root env e H D hDepth hm hm0 hml hmH he hv hEnv hLit
  have hprofile:=calibrate e.operationBound PlayerSpecificAlgebraicExpressionPrimitiveCost.coefficient (size H k D) _ _
    (PlayerSpecificResourceCostProfile.cubic _ (size H k D))
  exact (hc.trans hprofile).trans (transfer e.operationBound _ _ _ _ (size_linear H k D))

end Blotto.PlayerSpecificAlgebraicExpressionFixedCost
