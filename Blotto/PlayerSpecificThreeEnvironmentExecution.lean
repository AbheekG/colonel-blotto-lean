import Blotto.PlayerSpecificThreeGeometrySourceCost

/-! The actual raw three-variable geometry transformation executes
four fixed local programs over one cached five-row input environment. -/
namespace Blotto.PlayerSpecificThreeEnvironmentExecution
open PlayerSpecificDensePolynomial PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def input (a : Input) : FixedArrayTable 5 Data := FixedArrayTable.ofFn ![a.budget,a.first,a.second,a.third,a.probability]
def programs : FixedArrayTable 4 (RationalExpression 5) := FixedArrayTable.ofFn
  ![.sub (.input 0) (.input 1),.sub (.input 0) (.input 2),.sub (.input 0) (.input 3),
    .mul (.input 3) (.sub (.literal 1) (.input 4))]

def run (model : RationalCostModel) (root : Candidate) (a : Input) : FixedArrayTable 4 Data×ℕ :=
  PlayerSpecificExpressionVectorExecution.run model root (input a) programs

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicThreeInput.environment root a := by
  rw [run,PlayerSpecificExpressionVectorExecution.value]
  unfold PlayerSpecificAlgebraicThreeInput.environment
  congr 1
  funext j
  fin_cases j <;> simp [programs,input,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicExpression.run]

theorem depth (j : Fin 4) : (programs.read j).depth≤3 := by fin_cases j <;> decide
theorem literals (j : Fin 4) : (programs.read j).LiteralHeights 1 := by
  fin_cases j <;> simp [programs,FixedArrayTable.read_ofFn,RationalExpression.LiteralHeights]
  exact PlayerSpecificPolynomialHeights.one_height

end Blotto.PlayerSpecificThreeEnvironmentExecution
