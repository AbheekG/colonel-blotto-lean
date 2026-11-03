import Blotto.PlayerSpecificAlgebraicExpressionOverhead

/-! One actual local expression node, including its backend and complete
caller frame, has a derived uniform source-price bound. -/
namespace Blotto.PlayerSpecificAlgebraicExpressionNodeCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem primitive_profile (C S R : ℕ) : 8000000000*R≤(C+8000000000)*(S+1)*R := by
  nlinarith only [Nat.zero_le (C*(S+1)*R),Nat.zero_le (S*R)]

theorem local_profile (C S R : ℕ) :
    (C+8000000000)*(S+1)*R+500*R≤(C+8000001000)*(S+1)*R := by
  nlinarith only [Nat.zero_le (S*R),Nat.zero_le R]

theorem primitive {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (e : RationalExpression k) (S : ℕ) (hS : 1≤S)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmS : HasHeight root.polynomial S) (he : HasHeight [root.interval.lo,root.interval.hi] S)
    (hv : root.interval.lo<root.interval.hi) (hEnv : ∀ j,Reduced root.polynomial (env.read j)) (hLit : e.LiteralHeights S)
    (hAll : PlayerSpecificAlgebraicExpressionNodes.All (fun a => HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) S) e) :
    PlayerSpecificAlgebraicExpressionOverhead.primitive model root env e≤
      (PlayerSpecificAlgebraicComparisonExecution.coefficient+8000000000)*(S+1)*
        model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let P:=fun a : RationalExpression k => HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) S
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hred : ∀ a : RationalExpression k,Reduced root.polynomial (PlayerSpecificAlgebraicExpression.run model root env a) :=
    fun a => PlayerSpecificAlgebraicExpression.reduced model root env a hm hm0 hEnv
  have hbinary : ∀ op (a b : RationalExpression k),PlayerSpecificAlgebraicExpressionNodes.All P a → PlayerSpecificAlgebraicExpressionNodes.All P b →
      (PlayerSpecificAlgebraicExpressionExecution.binary model root op
        (PlayerSpecificAlgebraicExpression.run model root env a) (PlayerSpecificAlgebraicExpression.run model root env b)).2≤
          (PlayerSpecificAlgebraicComparisonExecution.coefficient+8000000000)*(S+1)*model.rat W := by
    intro op a b ha hb
    have hc:=PlayerSpecificAlgebraicExpressionPrimitiveCost.binary_cost model root op _ _ S hm hm0 hml (hred a) (hred b) hmS
      (PlayerSpecificAlgebraicExpressionNodes.head P a ha) (PlayerSpecificAlgebraicExpressionNodes.head P b hb) hS
    exact hc.trans (primitive_profile PlayerSpecificAlgebraicComparisonExecution.coefficient S (model.rat W))
  have hcompare : ∀ (a b : RationalExpression k),PlayerSpecificAlgebraicExpressionNodes.All P a → PlayerSpecificAlgebraicExpressionNodes.All P b →
      (PlayerSpecificAlgebraicComparisonExecution.run model root
        (PlayerSpecificAlgebraicExpression.run model root env a) (PlayerSpecificAlgebraicExpression.run model root env b)).2≤
          (PlayerSpecificAlgebraicComparisonExecution.coefficient+8000000000)*(S+1)*model.rat W := by
    intro a b ha hb
    have hc:=PlayerSpecificAlgebraicComparisonExecution.cost model root _ _ S hm hm0 hml hmS he hv
      (PlayerSpecificAlgebraicExpressionNodes.head P a ha) (PlayerSpecificAlgebraicExpressionNodes.head P b hb)
      (by have h:=(hred a).2; omega) (by have h:=(hred b).2; omega) hS
    exact hc.trans (Nat.mul_le_mul_right (model.rat W) (Nat.mul_le_mul_right (S+1) (Nat.le_add_right _ _)))
  cases e with
  | input j => exact Nat.zero_le _
  | literal q =>
    exact (PlayerSpecificAlgebraicExpressionPrimitiveCost.constant_cost model root q S hm hm0 hml hmS hLit hS).trans
      (primitive_profile PlayerSpecificAlgebraicComparisonExecution.coefficient S (model.rat W))
  | add a b => exact hbinary .add a b hAll.2.1 hAll.2.2
  | sub a b => exact hbinary .subtract a b hAll.2.1 hAll.2.2
  | mul a b => exact hbinary .multiply a b hAll.2.1 hAll.2.2
  | div a b => exact hbinary .divide a b hAll.2.1 hAll.2.2
  | minimum a b | maximum a b => exact hcompare a b hAll.2.1 hAll.2.2
  | ifLe a b yes no => exact hcompare a b hAll.2.1 hAll.2.2.1

theorem bound {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (e : RationalExpression k) (S : ℕ) (hk : k≤S) (hS : 10≤S)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmS : HasHeight root.polynomial S) (he : HasHeight [root.interval.lo,root.interval.hi] S)
    (hv : root.interval.lo<root.interval.hi) (hEnv : ∀ j,Reduced root.polynomial (env.read j)) (hLit : e.LiteralHeights S)
    (hAll : PlayerSpecificAlgebraicExpressionNodes.All (fun a => HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) S) e) :
    PlayerSpecificAlgebraicExpressionOverhead.localPrice model root env e≤PlayerSpecificAlgebraicExpressionPrimitiveCost.work model S := by
  have hp:=primitive model root env e S (by omega) hm hm0 hml hmS he hv hEnv hLit hAll
  have hf:=PlayerSpecificAlgebraicExpressionFrames.bound model root env e S hk hS hm hm0 hml hmS he hEnv hLit hAll
  exact (Nat.add_le_add hp hf).trans (local_profile PlayerSpecificAlgebraicComparisonExecution.coefficient S
    (model.rat (PlayerSpecificAlgebraicComparisonExecution.width S)))

end Blotto.PlayerSpecificAlgebraicExpressionNodeCost
