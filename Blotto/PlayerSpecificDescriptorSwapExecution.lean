import Blotto.PlayerSpecificNestedEndpointProfileSourceCost

/-! The actual fixed coordinate swap prices original/returned arrays
and the retained finite permutation indices. No field arithmetic runs. -/
namespace Blotto.PlayerSpecificDescriptorSwapExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor 3 slots) : Descriptor 3 slots×ℕ :=
  let result:=PlayerSpecificAlgebraicDescriptorSwap.swap d
  let env:=PlayerSpecificDescriptorPadExecution.environment
  (result,price model (PlayerSpecificDescriptorProgramExecution.frame root env d)+
    price model (PlayerSpecificDescriptorProgramExecution.frame root env result)+
    price model (PlayerSpecificAlgebraicCallerFrame.run [] [1,0,2]))

theorem value {slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor 3 slots) :
    (run model root d).1=PlayerSpecificAlgebraicDescriptorSwap.swap d := rfl
theorem packing (model : RationalCostModel) : price model (PlayerSpecificAlgebraicCallerFrame.run [] [1,0,2])=7 := rfl

end Blotto.PlayerSpecificDescriptorSwapExecution
