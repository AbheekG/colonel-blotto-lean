import Blotto.PlayerSpecificThreePositiveGeometrySourceCost

/-! The actual ordered preparation executes one measured test and
only its chosen geometry/exceptional continuation. -/
namespace Blotto.PlayerSpecificOrderedThreeExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 3 9×ℕ :=
  let tested:=PlayerSpecificThreePositiveExecution.run model root a
  let result:=if tested.1 then PlayerSpecificThreePositiveGeometryExecution.run model root a
    else PlayerSpecificThreeExceptionalExecution.run model root a
  (result.1,tested.2+result.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicOrderedThree.prepare model root a := by
  simp only [run,PlayerSpecificThreePositiveExecution.value,PlayerSpecificAlgebraicOrderedThree.prepare]
  split <;> simp_all only [PlayerSpecificThreePositiveGeometryExecution.value,PlayerSpecificThreeExceptionalExecution.value]

end Blotto.PlayerSpecificOrderedThreeExecution
