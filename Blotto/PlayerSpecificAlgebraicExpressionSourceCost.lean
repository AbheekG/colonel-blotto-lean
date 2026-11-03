import Blotto.PlayerSpecificAlgebraicExpressionNodeCost

/-! Complete executing expression cost. The operation bound includes
only the larger conditional continuation, matching single-path execution. -/
namespace Blotto.PlayerSpecificAlgebraicExpressionSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem sum_two (A B W : ℕ) : A*W+B*W+W=(A+B+1)*W := by ring
theorem sum_three (A B C W : ℕ) : A*W+B*W+C*W+W=(A+B+C+1)*W := by ring

theorem cost {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (e : RationalExpression k) (S : ℕ) (hk : k≤S) (hS : 10≤S)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmS : HasHeight root.polynomial S) (he : HasHeight [root.interval.lo,root.interval.hi] S)
    (hv : root.interval.lo<root.interval.hi) (hEnv : ∀ j,Reduced root.polynomial (env.read j)) (hLit : e.LiteralHeights S)
    (hAll : PlayerSpecificAlgebraicExpressionNodes.All (fun a => HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) S) e) :
    (PlayerSpecificAlgebraicExpressionExecution.run model root env e).2≤
      e.operationBound*PlayerSpecificAlgebraicExpressionPrimitiveCost.work model S := by
  let P:=fun a : RationalExpression k => HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) S
  let W:=PlayerSpecificAlgebraicExpressionPrimitiveCost.work model S
  have hnode : ∀ a : RationalExpression k,a.LiteralHeights S → PlayerSpecificAlgebraicExpressionNodes.All P a →
      PlayerSpecificAlgebraicExpressionOverhead.localPrice model root env a≤W := fun a hLiteral hNodes =>
    PlayerSpecificAlgebraicExpressionNodeCost.bound model root env a S hk hS hm hm0 hml hmS he hv hEnv hLiteral hNodes
  revert hLit hAll
  induction e with
  | input j =>
    intro hLit hAll
    rw [PlayerSpecificAlgebraicExpressionOverhead.cost_equation]
    simpa only [RationalExpression.operationBound,Nat.one_mul] using hnode (.input j) hLit hAll
  | literal q =>
    intro hLit hAll
    rw [PlayerSpecificAlgebraicExpressionOverhead.cost_equation]
    simpa only [RationalExpression.operationBound,Nat.one_mul] using hnode (.literal q) hLit hAll
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    intro hLit hAll
    have hA:=ha hLit.1 hAll.2.1
    have hB:=hb hLit.2 hAll.2.2
    have hCurrent:=hnode _ hLit hAll
    rw [PlayerSpecificAlgebraicExpressionOverhead.cost_equation]
    have hsum:=Nat.add_le_add (Nat.add_le_add hA hB) hCurrent
    apply hsum.trans
    rw [sum_two]
    apply Nat.mul_le_mul_right W
    simp only [RationalExpression.operationBound]
    omega
  | ifLe a b yes no ha hb hy hn =>
    intro hLit hAll
    have hA:=ha hLit.1 hAll.2.1
    have hB:=hb hLit.2.1 hAll.2.2.1
    have hY:=hy hLit.2.2.1 hAll.2.2.2.1
    have hN:=hn hLit.2.2.2 hAll.2.2.2.2
    have hCurrent:=hnode _ hLit hAll
    have hselected :
        (if PlayerSpecificAlgebraicPairStep.le model root (PlayerSpecificAlgebraicExpression.run model root env a)
          (PlayerSpecificAlgebraicExpression.run model root env b) then PlayerSpecificAlgebraicExpressionExecution.run model root env yes
          else PlayerSpecificAlgebraicExpressionExecution.run model root env no).2≤max yes.operationBound no.operationBound*W := by
      split
      · exact hY.trans (Nat.mul_le_mul_right W (le_max_left _ _))
      · exact hN.trans (Nat.mul_le_mul_right W (le_max_right _ _))
    rw [PlayerSpecificAlgebraicExpressionOverhead.cost_equation]
    have hsum:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hA hB) hselected) hCurrent
    apply hsum.trans_eq
    exact sum_three a.operationBound b.operationBound (max yes.operationBound no.operationBound) W

end Blotto.PlayerSpecificAlgebraicExpressionSourceCost
