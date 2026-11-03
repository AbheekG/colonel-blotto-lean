import Blotto.PlayerSpecificOverlapEnvironmentSourceCost

/-! A cached overlap row evaluates its weight and positivity comparison
once. The two endpoint vectors execute only the reached fallback/curve
programs. All original/output rows and enclosing returns are priced. -/
namespace Blotto.PlayerSpecificCachedOverlapRowExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def weightPrograms : FixedArrayTable 1 (RationalExpression 16) := FixedArrayTable.ofFn (fun _ => OverlapFormulaCode.weight)
def firstPrograms (fallback : Bool) : FixedArrayTable 4 (RationalExpression 16) :=
  if fallback then FixedArrayTable.ofFn OverlapFormulaCode.fallback
  else FixedArrayTable.ofFn (OverlapFormulaCode.curve OverlapFormulaCode.lower)
def secondPrograms (fallback : Bool) : FixedArrayTable 4 (RationalExpression 16) :=
  if fallback then FixedArrayTable.ofFn OverlapFormulaCode.fallback
  else FixedArrayTable.ofFn (OverlapFormulaCode.curve OverlapFormulaCode.upper)
def fields (r : Data×(FixedArrayTable 4 Data×FixedArrayTable 4 Data)) : FixedArrayTable 9 Data :=
  FixedArrayTable.ofFn ![r.1,r.2.1.read 0,r.2.1.read 1,r.2.1.read 2,r.2.1.read 3,r.2.2.read 0,r.2.2.read 1,r.2.2.read 2,r.2.2.read 3]
def run (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 16 Data) :
    (Data×(FixedArrayTable 4 Data×FixedArrayTable 4 Data))×ℕ :=
  let evaluated:=PlayerSpecificExpressionVectorExecution.run model root env weightPrograms
  let weight:=evaluated.1.read 0
  let zero:=PlayerSpecificFieldCombinationContract.constant root.polynomial 0
  let tested:=PlayerSpecificAlgebraicComparisonExecution.run model root weight zero.1
  let first:=PlayerSpecificExpressionVectorExecution.run model root env (firstPrograms tested.1)
  let second:=PlayerSpecificExpressionVectorExecution.run model root env (secondPrograms tested.1)
  let result:Data×(FixedArrayTable 4 Data×FixedArrayTable 4 Data):=(weight,first.1,second.1)
  (result,evaluated.2+price model zero.2+tested.2+first.2+second.2+
    price model (PlayerSpecificExpressionVectorExecution.frame root env (fields result))+price model (List.replicate 5 (.control 1)))

theorem conditional_value (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 16 Data)
    (left right yes no : RationalExpression 16) :
    PlayerSpecificAlgebraicExpression.run model root env (.ifLe left right yes no)=
      if PlayerSpecificAlgebraicPairStep.le model root (PlayerSpecificAlgebraicExpression.run model root env left)
        (PlayerSpecificAlgebraicExpression.run model root env right) then PlayerSpecificAlgebraicExpression.run model root env yes
      else PlayerSpecificAlgebraicExpression.run model root env no := rfl

theorem selected_table_value (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 16 Data)
    (left right : RationalExpression 16) (yes no : Fin 4 → RationalExpression 16) :
    (PlayerSpecificExpressionVectorExecution.run model root env
      (if PlayerSpecificAlgebraicPairStep.le model root (PlayerSpecificAlgebraicExpression.run model root env left)
        (PlayerSpecificAlgebraicExpression.run model root env right) then FixedArrayTable.ofFn yes else FixedArrayTable.ofFn no)).1=
      FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env (.ifLe left right (yes j) (no j))) := by
  rw [PlayerSpecificExpressionVectorExecution.value]
  by_cases hb : PlayerSpecificAlgebraicPairStep.le model root (PlayerSpecificAlgebraicExpression.run model root env left)
      (PlayerSpecificAlgebraicExpression.run model root env right)=true
  · simp only [FixedArrayTable.read_ofFn,conditional_value,hb,ite_true]
  · simp only [FixedArrayTable.read_ofFn,conditional_value,hb,Bool.false_eq_true,ite_false]

theorem value (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 16 Data) :
    (run model root env).1=PlayerSpecificAlgebraicOverlapTable.row model root env := by
  let b:=PlayerSpecificAlgebraicPairStep.le model root (PlayerSpecificAlgebraicExpression.run model root env OverlapFormulaCode.weight)
    (PlayerSpecificAlgebraicField.constant root.polynomial 0)
  have hp : (PlayerSpecificExpressionVectorExecution.run model root env (firstPrograms b)).1=
      FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env (OverlapFormulaCode.safeP j)) :=
    selected_table_value model root env OverlapFormulaCode.weight (.literal 0) OverlapFormulaCode.fallback (OverlapFormulaCode.curve OverlapFormulaCode.lower)
  have hq : (PlayerSpecificExpressionVectorExecution.run model root env (secondPrograms b)).1=
      FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env (OverlapFormulaCode.safeQ j)) :=
    selected_table_value model root env OverlapFormulaCode.weight (.literal 0) OverlapFormulaCode.fallback (OverlapFormulaCode.curve OverlapFormulaCode.upper)
  simp only [run,PlayerSpecificExpressionVectorExecution.read_value,weightPrograms,FixedArrayTable.read_ofFn,
    PlayerSpecificFieldCombinationContract.constant_value,PlayerSpecificAlgebraicComparisonExecution.value]
  rw [hp,hq]
  rfl
theorem packing (model : RationalCostModel) : price model (List.replicate 5 (.control 1))=10 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 16 Data) :
    (run model root env).2=(PlayerSpecificExpressionVectorExecution.run model root env weightPrograms).2+
      price model (PlayerSpecificFieldCombinationContract.constant root.polynomial 0).2+
      (PlayerSpecificAlgebraicComparisonExecution.run model root (PlayerSpecificAlgebraicExpression.run model root env OverlapFormulaCode.weight)
        (PlayerSpecificAlgebraicField.constant root.polynomial 0)).2+
      (PlayerSpecificExpressionVectorExecution.run model root env (firstPrograms (PlayerSpecificAlgebraicPairStep.le model root
        (PlayerSpecificAlgebraicExpression.run model root env OverlapFormulaCode.weight) (PlayerSpecificAlgebraicField.constant root.polynomial 0)))).2+
      (PlayerSpecificExpressionVectorExecution.run model root env (secondPrograms (PlayerSpecificAlgebraicPairStep.le model root
        (PlayerSpecificAlgebraicExpression.run model root env OverlapFormulaCode.weight) (PlayerSpecificAlgebraicField.constant root.polynomial 0)))).2+
      price model (PlayerSpecificExpressionVectorExecution.frame root env (fields (run model root env).1))+10 := by
  simp only [run,PlayerSpecificExpressionVectorExecution.read_value,weightPrograms,FixedArrayTable.read_ofFn,
    PlayerSpecificFieldCombinationContract.constant_value,PlayerSpecificAlgebraicComparisonExecution.value,packing]

end Blotto.PlayerSpecificCachedOverlapRowExecution
