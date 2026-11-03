import Blotto.PlayerSpecificAlgebraicExpressionFrames

/-! Exact source ledgers for one interpreter node, apart from its cached
children. These proof-side ledgers never execute a second sampler path. -/
namespace Blotto.PlayerSpecificAlgebraicExpressionOverhead
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def primitive {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data) : RationalExpression k → ℕ
  | .input _ => 0
  | .literal q => price model (PlayerSpecificFieldCombinationContract.constant root.polynomial q).2
  | .add a b => (PlayerSpecificAlgebraicExpressionExecution.binary model root .add
      (PlayerSpecificAlgebraicExpression.run model root env a) (PlayerSpecificAlgebraicExpression.run model root env b)).2
  | .sub a b => (PlayerSpecificAlgebraicExpressionExecution.binary model root .subtract
      (PlayerSpecificAlgebraicExpression.run model root env a) (PlayerSpecificAlgebraicExpression.run model root env b)).2
  | .mul a b => (PlayerSpecificAlgebraicExpressionExecution.binary model root .multiply
      (PlayerSpecificAlgebraicExpression.run model root env a) (PlayerSpecificAlgebraicExpression.run model root env b)).2
  | .div a b => (PlayerSpecificAlgebraicExpressionExecution.binary model root .divide
      (PlayerSpecificAlgebraicExpression.run model root env a) (PlayerSpecificAlgebraicExpression.run model root env b)).2
  | .minimum a b | .maximum a b | .ifLe a b _ _ => (PlayerSpecificAlgebraicComparisonExecution.run model root
      (PlayerSpecificAlgebraicExpression.run model root env a) (PlayerSpecificAlgebraicExpression.run model root env b)).2

def localPrice {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data) (e : RationalExpression k) : ℕ :=
  primitive model root env e+PlayerSpecificAlgebraicExpressionFrames.price model root env e

theorem cost_equation {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data) (e : RationalExpression k) :
    (PlayerSpecificAlgebraicExpressionExecution.run model root env e).2=
      match e with
      | .input _ | .literal _ => localPrice model root env e
      | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b =>
          (PlayerSpecificAlgebraicExpressionExecution.run model root env a).2+
            (PlayerSpecificAlgebraicExpressionExecution.run model root env b).2+localPrice model root env e
      | .ifLe a b yes no =>
          let upper:=PlayerSpecificAlgebraicPairStep.le model root
            (PlayerSpecificAlgebraicExpression.run model root env a) (PlayerSpecificAlgebraicExpression.run model root env b)
          (PlayerSpecificAlgebraicExpressionExecution.run model root env a).2+
            (PlayerSpecificAlgebraicExpressionExecution.run model root env b).2+
            (if upper then PlayerSpecificAlgebraicExpressionExecution.run model root env yes else
              PlayerSpecificAlgebraicExpressionExecution.run model root env no).2+localPrice model root env e := by
  cases e <;> simp only [PlayerSpecificAlgebraicExpressionExecution.run,localPrice,primitive,
    PlayerSpecificAlgebraicExpressionFrames.price,PlayerSpecificAlgebraicExpressionFrames.rows,PlayerSpecificAlgebraicExpressionFrames.words,
    PlayerSpecificAlgebraicExpressionExecution.value,PlayerSpecificAlgebraicExpressionExecution.binary_value,
    PlayerSpecificFieldCombinationContract.constant_value,PlayerSpecificAlgebraicComparisonExecution.value,
    PlayerSpecificAlgebraicExpression.run,Nat.zero_add,Nat.add_assoc]
  all_goals split <;> simp_all only [PlayerSpecificAlgebraicExpressionExecution.value] <;> omega

end Blotto.PlayerSpecificAlgebraicExpressionOverhead
