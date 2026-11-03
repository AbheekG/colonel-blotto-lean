import Blotto.PlayerSpecificResidualTableSourceCost

/-! A shifted endpoint executes its one addition once; the two
unchanged coordinates and all input/return indices are priced. -/
namespace Blotto.PlayerSpecificDescriptorShiftRowExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment (s : Data) (a : FixedArrayTable 3 Data) : FixedArrayTable 4 Data :=
  FixedArrayTable.ofFn ![a.read 0,a.read 1,a.read 2,s]
def programs : FixedArrayTable 3 (RationalExpression 4) :=
  FixedArrayTable.ofFn ![.input 0,.input 1,.add (.input 2) (.input 3)]
def run (model : RationalCostModel) (root : Candidate) (s : Data) (a : FixedArrayTable 3 Data) : FixedArrayTable 3 Data×ℕ :=
  PlayerSpecificExpressionVectorExecution.run model root (environment s a) programs

theorem value (model : RationalCostModel) (root : Candidate) (s : Data) (a : FixedArrayTable 3 Data) :
    (run model root s a).1=PlayerSpecificAlgebraicDescriptorShift.row root s a := by
  rw [run,PlayerSpecificExpressionVectorExecution.value,PlayerSpecificAlgebraicDescriptorShift.row]
  apply congrArg FixedArrayTable.ofFn
  funext j
  fin_cases j <;> simp [programs,environment,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicExpression.run]

theorem depth (j : Fin 3) : (programs.read j).depth≤1 := by
  fin_cases j <;> decide
theorem literals (j : Fin 3) (H : ℕ) : (programs.read j).LiteralHeights H := by
  fin_cases j <;> trivial
theorem operations : PlayerSpecificExpressionVectorExecution.operations programs=5 := by decide

end Blotto.PlayerSpecificDescriptorShiftRowExecution
