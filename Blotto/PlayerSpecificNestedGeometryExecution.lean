import Blotto.PlayerSpecificNestedZeroSourceCost

/-! The reached conditional geometry computes its environment and
table once, then shifts each retained endpoint once. -/
namespace Blotto.PlayerSpecificNestedGeometryExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) : Descriptor 3 9×ℕ :=
  let env:=PlayerSpecificNestedParameterExecution.firstEnvironment model root a extra
  let geometry:=PlayerSpecificThreeGeometryExecution.run model root env.1
  let shifted:=PlayerSpecificDescriptorShiftExecution.run model root extra geometry.1
  (shifted.1,env.2+geometry.2+shifted.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) :
    (run model root a extra).1=PlayerSpecificAlgebraicDescriptorShift.shift root extra
      (PlayerSpecificAlgebraicThreeGeometry.prepare model root (firstEnvironment model root a extra)) := by
  simp only [run,PlayerSpecificNestedParameterExecution.first_value,PlayerSpecificThreeGeometryExecution.value,
    PlayerSpecificDescriptorShiftExecution.value]

theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) :
    (run model root a extra).2=(PlayerSpecificNestedParameterExecution.firstEnvironment model root a extra).2+
      (PlayerSpecificThreeGeometryExecution.run model root (firstEnvironment model root a extra)).2+
      (PlayerSpecificDescriptorShiftExecution.run model root extra
        (PlayerSpecificThreeGeometryExecution.run model root (firstEnvironment model root a extra)).1).2+2 := by
  simp only [run,PlayerSpecificNestedParameterExecution.first_value,packing]

end Blotto.PlayerSpecificNestedGeometryExecution
