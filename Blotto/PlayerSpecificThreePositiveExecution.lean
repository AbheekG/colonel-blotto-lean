import Blotto.PlayerSpecificThreeExceptionalSourceCost

/-! Actual measured positive-geometry test. The sum and exact fit
comparison execute once and their rows remain retained until return. -/
namespace Blotto.PlayerSpecificThreePositiveExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (root : Candidate) (a : Input) (combined : Data) : Trace :=
  PlayerSpecificExpressionVectorExecution.frame root (PlayerSpecificThreeEnvironmentExecution.input a)
    (FixedArrayTable.ofFn (fun _ : Fin 1 => combined))

def run (model : RationalCostModel) (root : Candidate) (a : Input) : Bool×ℕ :=
  let combined:=PlayerSpecificFieldCombination.run false root.polynomial a.first a.second
  let tested:=PlayerSpecificAlgebraicComparisonExecution.run model root combined.1 a.budget
  (!tested.1,price model combined.2+tested.2+price model (frame root a combined.1))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicThreeInput.positive model root a := by
  simp only [run,PlayerSpecificFieldCombination.value,PlayerSpecificAlgebraicComparisonExecution.value,
    Bool.false_eq_true,ite_false,PlayerSpecificAlgebraicThreeInput.positive]

end Blotto.PlayerSpecificThreePositiveExecution
