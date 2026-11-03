import Blotto.PlayerSpecificAlgebraicTerminalGroupBounds
import Blotto.RealExpression

/-! Executable evaluation of the retained local coupling expression
language in the selected algebraic field. Subexpressions are evaluated
once, and conditionals evaluate only the selected continuation. -/
namespace Blotto.PlayerSpecificAlgebraicExpression
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data) : RationalExpression k → Data
  | .input j => env.read j
  | .literal q => PlayerSpecificAlgebraicField.constant root.polynomial q
  | .add a b => let u:=run model root env a; let v:=run model root env b
      PlayerSpecificAlgebraicField.plus root.polynomial u v
  | .sub a b => let u:=run model root env a; let v:=run model root env b
      PlayerSpecificAlgebraicField.minus root.polynomial u v
  | .mul a b => let u:=run model root env a; let v:=run model root env b
      PlayerSpecificAlgebraicField.times root.polynomial u v
  | .div a b => let u:=run model root env a; let v:=run model root env b
      PlayerSpecificAlgebraicField.divide root.polynomial u v
  | .minimum a b => let u:=run model root env a; let v:=run model root env b
      if PlayerSpecificAlgebraicPairStep.le model root u v then u else v
  | .maximum a b => let u:=run model root env a; let v:=run model root env b
      if PlayerSpecificAlgebraicPairStep.le model root u v then v else u
  | .ifLe a b yes no => let u:=run model root env a; let v:=run model root env b
      if PlayerSpecificAlgebraicPairStep.le model root u v then run model root env yes else run model root env no

noncomputable def realEnv {k : ℕ} (env : FixedArrayTable k Data) (x : ℝ) : FixedArrayTable k ℝ :=
  FixedArrayTable.ofFn (fun j => realEvaluate (env.read j) x)

theorem reduced {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (e : RationalExpression k) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hEnv : ∀ j,Reduced root.polynomial (env.read j)) : Reduced root.polynomial (run model root env e) := by
  induction e with
  | input j => exact hEnv j
  | literal q => exact PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0
  | add a b _ _ => exact PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0
  | sub a b _ _ => exact PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0
  | mul a b _ _ => exact PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0
  | div a b _ _ => exact PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0
  | minimum a b ha hb => simp only [run]; split; exact ha; exact hb
  | maximum a b ha hb => simp only [run]; split; exact hb; exact ha
  | ifLe a b yes no _ _ hy hn => simp only [run]; split; exact hy; exact hn

end Blotto.PlayerSpecificAlgebraicExpression
