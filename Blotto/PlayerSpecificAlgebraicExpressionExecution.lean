import Blotto.PlayerSpecificFiniteResourceEntryCost
import Blotto.PlayerSpecificAlgebraicExpressionHeights

/-! Measured executing local algebraic expressions. Each subexpression
and exact comparison is retained once; only the selected conditional
continuation is evaluated. Actual backend/copy/index/control work is priced. -/
namespace Blotto.PlayerSpecificAlgebraicExpressionExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (root : Candidate) (rows : List Data) (words : List ℕ) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run ([root.polynomial,[root.interval.lo,root.interval.hi]]++rows) words

def binary (model : RationalCostModel) (root : Candidate) (op : Arithmetic) (a b : Data) : Data×ℕ :=
  match op with
  | .add => let r:=PlayerSpecificFieldCombination.run false root.polynomial a b; (r.1,price model r.2)
  | .subtract => let r:=PlayerSpecificFieldCombination.run true root.polynomial a b; (r.1,price model r.2)
  | .multiply => PlayerSpecificModularExecution.run model root.polynomial b a
  | .divide => PlayerSpecificFieldDivisionExecution.run model root.polynomial a b

theorem binary_value (model : RationalCostModel) (root : Candidate) (op : Arithmetic) (a b : Data) :
    (binary model root op a b).1=match op with
      | .add => PlayerSpecificAlgebraicField.plus root.polynomial a b
      | .subtract => PlayerSpecificAlgebraicField.minus root.polynomial a b
      | .multiply => PlayerSpecificAlgebraicField.times root.polynomial a b
      | .divide => PlayerSpecificAlgebraicField.divide root.polynomial a b := by
  cases op <;> simp only [binary,PlayerSpecificFieldCombination.value,PlayerSpecificModularExecution.value,
    PlayerSpecificFieldDivisionExecution.value,Bool.false_eq_true,ite_false,ite_true,PlayerSpecificAlgebraicField.times]

def run {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data) : RationalExpression k → Data×ℕ
  | .input j => let result:=env.read j
      (result,price model (frame root [result] [k,j.val,1]))
  | .literal q => let result:=PlayerSpecificFieldCombinationContract.constant root.polynomial q
      (result.1,price model result.2+price model (frame root [[q],result.1] [k,2]))
  | .add a b =>
      let u:=run model root env a; let v:=run model root env b
      let result:=binary model root .add u.1 v.1
      (result.1,u.2+v.2+result.2+price model (frame root [u.1,v.1,result.1] [k,3]))
  | .sub a b =>
      let u:=run model root env a; let v:=run model root env b
      let result:=binary model root .subtract u.1 v.1
      (result.1,u.2+v.2+result.2+price model (frame root [u.1,v.1,result.1] [k,4]))
  | .mul a b =>
      let u:=run model root env a; let v:=run model root env b
      let result:=binary model root .multiply u.1 v.1
      (result.1,u.2+v.2+result.2+price model (frame root [u.1,v.1,result.1] [k,5]))
  | .div a b =>
      let u:=run model root env a; let v:=run model root env b
      let result:=binary model root .divide u.1 v.1
      (result.1,u.2+v.2+result.2+price model (frame root [u.1,v.1,result.1] [k,6]))
  | .minimum a b =>
      let u:=run model root env a; let v:=run model root env b
      let compared:=PlayerSpecificAlgebraicComparisonExecution.run model root u.1 v.1
      let result:=if compared.1 then u.1 else v.1
      (result,u.2+v.2+compared.2+price model (frame root [u.1,v.1,result] [k,7]))
  | .maximum a b =>
      let u:=run model root env a; let v:=run model root env b
      let compared:=PlayerSpecificAlgebraicComparisonExecution.run model root u.1 v.1
      let result:=if compared.1 then v.1 else u.1
      (result,u.2+v.2+compared.2+price model (frame root [u.1,v.1,result] [k,8]))
  | .ifLe a b yes no =>
      let u:=run model root env a; let v:=run model root env b
      let compared:=PlayerSpecificAlgebraicComparisonExecution.run model root u.1 v.1
      let result:=if compared.1 then run model root env yes else run model root env no
      (result.1,u.2+v.2+compared.2+result.2+price model (frame root [u.1,v.1,result.1] [k,9]))

theorem value {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data) (e : RationalExpression k) :
    (run model root env e).1=PlayerSpecificAlgebraicExpression.run model root env e := by
  induction e with
  | input j => rfl
  | literal q => exact PlayerSpecificFieldCombinationContract.constant_value root.polynomial q
  | add a b ha hb => simp only [run,ha,hb,binary_value,PlayerSpecificAlgebraicExpression.run]
  | sub a b ha hb => simp only [run,ha,hb,binary_value,PlayerSpecificAlgebraicExpression.run]
  | mul a b ha hb => simp only [run,ha,hb,binary_value,PlayerSpecificAlgebraicExpression.run]
  | div a b ha hb => simp only [run,ha,hb,binary_value,PlayerSpecificAlgebraicExpression.run]
  | minimum a b ha hb => simp only [run,ha,hb,PlayerSpecificAlgebraicComparisonExecution.value,PlayerSpecificAlgebraicExpression.run]
  | maximum a b ha hb => simp only [run,ha,hb,PlayerSpecificAlgebraicComparisonExecution.value,PlayerSpecificAlgebraicExpression.run]
  | ifLe a b yes no ha hb hy hn =>
    simp only [run,ha,hb,PlayerSpecificAlgebraicComparisonExecution.value,PlayerSpecificAlgebraicExpression.run]
    split <;> simp_all only

end Blotto.PlayerSpecificAlgebraicExpressionExecution
