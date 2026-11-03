import Blotto.PlayerSpecificOriginalTerminalPreparationCost
import Blotto.PlayerSpecificAlgebraicExpressionFixedCost

/-! Cached finite local-program evaluation. Every expression executes
once, and every result is read from its retained measured table. -/
namespace Blotto.PlayerSpecificExpressionVectorExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame {k m : ℕ} (root : Candidate) (env : FixedArrayTable k Data) (result : FixedArrayTable m Data) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run
    ([root.polynomial,[root.interval.lo,root.interval.hi]]++List.ofFn env.read++List.ofFn result.read)
    ([k,m,1]++List.range k++List.range m++List.range m)

def run {k m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (program : FixedArrayTable m (RationalExpression k)) : FixedArrayTable m Data×ℕ :=
  let measured:=FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpressionExecution.run model root env (program.read j))
  let result:=FixedArrayTable.ofFn (fun j => (measured.read j).1)
  (result,(∑ j : Fin m,(measured.read j).2)+price model (frame root env result))

theorem read_value {k m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (program : FixedArrayTable m (RationalExpression k)) (j : Fin m) :
    ((run model root env program).1.read j)=PlayerSpecificAlgebraicExpression.run model root env (program.read j) := by
  simp only [run,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicExpressionExecution.value]

theorem value {k m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (program : FixedArrayTable m (RationalExpression k)) :
    (run model root env program).1=FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env (program.read j)) := by
  simp only [run,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicExpressionExecution.value]

def operations {k m : ℕ} (program : FixedArrayTable m (RationalExpression k)) : ℕ := ∑ j : Fin m,(program.read j).operationBound

theorem price_equation {k m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (program : FixedArrayTable m (RationalExpression k)) :
    (run model root env program).2=(∑ j : Fin m,(PlayerSpecificAlgebraicExpressionExecution.run model root env (program.read j)).2)+
      price model (frame root env (run model root env program).1) := by
  simp only [run,FixedArrayTable.read_ofFn]

end Blotto.PlayerSpecificExpressionVectorExecution
