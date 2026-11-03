import Blotto.PlayerSpecificNestedFamilySourceCost

/-! The actual outer location retains the midpoint, its field scalar
and the requested location program once, with every source price. -/
namespace Blotto.PlayerSpecificNestedLocationExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) : Data×ℕ :=
  let midpoint:=PlayerSpecificMidpointExecution.run model K outer
  let scalar:=PlayerSpecificFieldCombinationContract.constant root.polynomial midpoint.1
  let result:=PlayerSpecificNestedParameterExecution.scalar model root a scalar.1 0
  (result.1,midpoint.2+price model scalar.2+result.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a K outer).1=PlayerSpecificAlgebraicNestedFirstDraw.location model root a K outer := by
  simp only [run,PlayerSpecificMidpointExecution.value,PlayerSpecificFieldCombinationContract.constant_value,
    PlayerSpecificNestedParameterExecution.scalar_value,PlayerSpecificAlgebraicNestedFirstDraw.location]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a K outer).2=(PlayerSpecificMidpointExecution.run model K outer).2+
      price model (PlayerSpecificFieldCombinationContract.constant root.polynomial (dyadicMidpointSample K outer)).2+
      (PlayerSpecificNestedParameterExecution.scalar model root a
        (PlayerSpecificAlgebraicField.constant root.polynomial (dyadicMidpointSample K outer)) 0).2+2 := by
  simp only [run,PlayerSpecificMidpointExecution.value,PlayerSpecificFieldCombinationContract.constant_value,packing]

end Blotto.PlayerSpecificNestedLocationExecution
