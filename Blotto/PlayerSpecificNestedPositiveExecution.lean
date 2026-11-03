import Blotto.PlayerSpecificDescriptorBinarySourceCost

/-! The first conditional test evaluates only its requested scalar,
then performs one exact comparison. Its boolean return is priced. -/
namespace Blotto.PlayerSpecificNestedPositiveExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) : Bool×ℕ :=
  let scalar:=PlayerSpecificNestedParameterExecution.scalar model root a extra 1
  let tested:=PlayerSpecificAlgebraicComparisonExecution.run model root scalar.1 []
  (!tested.1,scalar.2+tested.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) :
    (run model root a extra).1=PlayerSpecificAlgebraicNestedFirstTable.positive model root a extra := by
  simp only [run,PlayerSpecificNestedParameterExecution.scalar_value,PlayerSpecificAlgebraicComparisonExecution.value,
    PlayerSpecificAlgebraicNestedFirstTable.positive]

theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl

end Blotto.PlayerSpecificNestedPositiveExecution
