import Blotto.PlayerSpecificNestedEndpointInputSourceCost

/-! Complete endpoint preparation retains one actual endpoint input,
one unordered three-variable table and its feasible eighteen-slot pad. -/
namespace Blotto.PlayerSpecificNestedEndpointProfileExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (useShort : Bool) : Descriptor 3 18×ℕ :=
  let input:=PlayerSpecificNestedEndpointInputExecution.run model root a useShort
  let table:=PlayerSpecificUnorderedThreeExecution.run model root input.1
  let padded:=PlayerSpecificDescriptorPadExecution.run model root table.1 9 0
  (padded.1,input.2+table.2+padded.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (useShort : Bool) :
    (run model root a useShort).1=PlayerSpecificAlgebraicDescriptorPad.pad
      (PlayerSpecificAlgebraicUnorderedThree.prepare model root (PlayerSpecificAlgebraicNestedSpecInput.endpoint root a useShort)) 9 0 := by
  simp only [run,PlayerSpecificNestedEndpointInputExecution.value,PlayerSpecificUnorderedThreeExecution.value,
    PlayerSpecificDescriptorPadExecution.value]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (useShort : Bool) :
    (run model root a useShort).2=(PlayerSpecificNestedEndpointInputExecution.run model root a useShort).2+
      (PlayerSpecificUnorderedThreeExecution.run model root (PlayerSpecificAlgebraicNestedSpecInput.endpoint root a useShort)).2+
      (PlayerSpecificDescriptorPadExecution.run model root
        (PlayerSpecificUnorderedThreeExecution.run model root (PlayerSpecificAlgebraicNestedSpecInput.endpoint root a useShort)).1 9 0).2+2 := by
  simp only [run,PlayerSpecificNestedEndpointInputExecution.value,packing]

end Blotto.PlayerSpecificNestedEndpointProfileExecution
