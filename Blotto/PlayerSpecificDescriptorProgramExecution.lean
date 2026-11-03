import Blotto.PlayerSpecificExpressionVectorSourceCost

/-! Measured finite segment-table materialization. Every weight and
endpoint expression executes once; outer/inner measured arrays retain
the results before the final descriptor arrays are constructed. -/
namespace Blotto.PlayerSpecificDescriptorProgramExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def rows {n m : ℕ} (d : Descriptor n m) : List Data :=
  List.ofFn d.weights.read++(List.ofFn (fun slot => List.ofFn (d.first.read slot).read)).flatten++
    (List.ofFn (fun slot => List.ofFn (d.second.read slot).read)).flatten

def frame {k n m : ℕ} (root : Candidate) (env : FixedArrayTable k Data) (d : Descriptor n m) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run
    ([root.polynomial,[root.interval.lo,root.interval.hi]]++List.ofFn env.read++rows d)
    ([k,n,m,1]++List.range k++List.range m++List.range m++
      (List.replicate m (List.range n++List.range n)).flatten)

def run {k n m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (weights : FixedArrayTable m (RationalExpression k))
    (first second : FixedArrayTable m (FixedArrayTable n (RationalExpression k))) : Descriptor n m×ℕ :=
  let w:=FixedArrayTable.ofFn (fun slot => PlayerSpecificAlgebraicExpressionExecution.run model root env (weights.read slot))
  let p:=FixedArrayTable.ofFn (fun slot => let expressions:=first.read slot
    FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpressionExecution.run model root env (expressions.read j)))
  let q:=FixedArrayTable.ofFn (fun slot => let expressions:=second.read slot
    FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpressionExecution.run model root env (expressions.read j)))
  let result:Descriptor n m:=⟨FixedArrayTable.ofFn (fun slot => (w.read slot).1),
    FixedArrayTable.ofFn (fun slot => let row:=p.read slot; FixedArrayTable.ofFn (fun j => (row.read j).1)),
    FixedArrayTable.ofFn (fun slot => let row:=q.read slot; FixedArrayTable.ofFn (fun j => (row.read j).1))⟩
  (result,(∑ slot : Fin m,(w.read slot).2)+(∑ slot : Fin m,∑ j : Fin n,((p.read slot).read j).2)+
    (∑ slot : Fin m,∑ j : Fin n,((q.read slot).read j).2)+price model (frame root env result))

theorem value {k n m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (weights : FixedArrayTable m (RationalExpression k))
    (first second : FixedArrayTable m (FixedArrayTable n (RationalExpression k))) :
    (run model root env weights first second).1=
      ⟨FixedArrayTable.ofFn (fun slot => PlayerSpecificAlgebraicExpression.run model root env (weights.read slot)),
        FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env ((first.read slot).read j))),
        FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env ((second.read slot).read j)))⟩ := by
  simp only [run,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicExpressionExecution.value]

def operations {k n m : ℕ} (weights : FixedArrayTable m (RationalExpression k))
    (first second : FixedArrayTable m (FixedArrayTable n (RationalExpression k))) : ℕ :=
  (∑ slot : Fin m,(weights.read slot).operationBound)+(∑ slot : Fin m,∑ j : Fin n,((first.read slot).read j).operationBound)+
    (∑ slot : Fin m,∑ j : Fin n,((second.read slot).read j).operationBound)

theorem price_equation {k n m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (weights : FixedArrayTable m (RationalExpression k))
    (first second : FixedArrayTable m (FixedArrayTable n (RationalExpression k))) :
    (run model root env weights first second).2=
      (∑ slot : Fin m,(PlayerSpecificAlgebraicExpressionExecution.run model root env (weights.read slot)).2)+
      (∑ slot : Fin m,∑ j : Fin n,(PlayerSpecificAlgebraicExpressionExecution.run model root env ((first.read slot).read j)).2)+
      (∑ slot : Fin m,∑ j : Fin n,(PlayerSpecificAlgebraicExpressionExecution.run model root env ((second.read slot).read j)).2)+
      price model (frame root env (run model root env weights first second).1) := by
  simp only [run,FixedArrayTable.read_ofFn]

end Blotto.PlayerSpecificDescriptorProgramExecution
