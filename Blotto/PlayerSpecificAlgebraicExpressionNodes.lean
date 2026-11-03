import Blotto.PlayerSpecificAlgebraicExpressionExecution

/-! Uniform proof-only certificates for every local expression node.
The executing interpreter evaluates only its selected conditional path. -/
namespace Blotto.PlayerSpecificAlgebraicExpressionNodes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def All {k : ℕ} (P : RationalExpression k → Prop) (e : RationalExpression k) : Prop :=
  P e ∧ match e with
    | .input _ | .literal _ => True
    | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => All P a ∧ All P b
    | .ifLe a b yes no => All P a ∧ All P b ∧ All P yes ∧ All P no

theorem head {k : ℕ} (P : RationalExpression k → Prop) (e : RationalExpression k) (h : All P e) : P e := by
  cases e <;> exact h.1

theorem heights {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (e : RationalExpression k) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (H D : ℕ) (hmH : HasHeight root.polynomial H) (hH : 1≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H)
    (hLit : e.LiteralHeights H) (hDepth : e.depth≤D) :
    All (fun a => HasHeight (PlayerSpecificAlgebraicExpression.run model root env a)
      (PlayerSpecificAlgebraicHeightEnvelope.iterate (D+1) H)) e := by
  have hout : ∀ a : RationalExpression k,a.LiteralHeights H → a.depth≤D →
      HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) (PlayerSpecificAlgebraicHeightEnvelope.iterate (D+1) H) := by
    intro a hLiteral hDegree
    exact mono (PlayerSpecificAlgebraicExpressionHeights.run_height model root env a hm hm0 hml H hmH hH hEnv hLiteral)
      (PlayerSpecificAlgebraicExpressionBudget.depth_mono H hDegree)
  revert hLit hDepth
  induction e with
  | input j => intro hLit hDepth; exact ⟨hout _ hLit hDepth,trivial⟩
  | literal q => intro hLit hDepth; exact ⟨hout _ hLit hDepth,trivial⟩
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    intro hLit hDepth
    refine ⟨hout _ hLit hDepth,ha hLit.1 ?_,hb hLit.2 ?_⟩
    all_goals simp only [RationalExpression.depth] at hDepth; omega
  | ifLe a b yes no ha hb hy hn =>
    intro hLit hDepth
    refine ⟨hout _ hLit hDepth,ha hLit.1 ?_,hb hLit.2.1 ?_,hy hLit.2.2.1 ?_,hn hLit.2.2.2 ?_⟩
    all_goals simp only [RationalExpression.depth] at hDepth; omega

end Blotto.PlayerSpecificAlgebraicExpressionNodes
