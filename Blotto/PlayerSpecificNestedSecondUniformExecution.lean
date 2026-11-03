import Blotto.PlayerSpecificNestedSecondInputSourceCost

/-! The second uniform component retains its actual input, ordered
three-variable preparation and mirror shift once each. -/
namespace Blotto.PlayerSpecificNestedSecondUniformExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) : Descriptor 3 9×ℕ :=
  let input:=PlayerSpecificNestedSecondInputExecution.run model root a p
  let table:=PlayerSpecificOrderedThreeExecution.run model root input.1
  let shifted:=PlayerSpecificDescriptorShiftExecution.run model root p.mirror table.1
  (shifted.1,input.2+table.2+shifted.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) :
    (run model root a p).1=PlayerSpecificAlgebraicNestedSecondUniform.prepare model root a p := by
  simp only [run,PlayerSpecificNestedSecondInputExecution.value,PlayerSpecificOrderedThreeExecution.value,
    PlayerSpecificDescriptorShiftExecution.value,PlayerSpecificAlgebraicNestedSecondUniform.prepare]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) :
    (run model root a p).2=(PlayerSpecificNestedSecondInputExecution.run model root a p).2+
      (PlayerSpecificOrderedThreeExecution.run model root (PlayerSpecificAlgebraicNestedSecondUniform.input root a p)).2+
      (PlayerSpecificDescriptorShiftExecution.run model root p.mirror
        (PlayerSpecificOrderedThreeExecution.run model root (PlayerSpecificAlgebraicNestedSecondUniform.input root a p)).1).2+2 := by
  simp only [run,PlayerSpecificNestedSecondInputExecution.value,packing]

end Blotto.PlayerSpecificNestedSecondUniformExecution
