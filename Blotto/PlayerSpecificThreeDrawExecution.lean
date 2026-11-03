import Blotto.PlayerSpecificSegmentDrawSourceCost

/-! Complete measured actual three-variable draw: prepare the selected
descriptor once and run the complete measured finite segment sampler. -/
namespace Blotto.PlayerSpecificThreeDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (bits : Fin (8*H+K) → Bool) : FixedArrayTable 3 Data×ℕ :=
  let prepared:=PlayerSpecificUnorderedThreeExecution.run model root a
  let result:=PlayerSpecificSegmentDrawExecution.run model root prepared.1 8 H K bits
  (result.1,prepared.2+result.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (bits : Fin (8*H+K) → Bool) :
    (run model root a H K bits).1=PlayerSpecificAlgebraicThreeDraw.draw model root a H K bits := by
  simp only [run,PlayerSpecificSegmentDrawExecution.value,PlayerSpecificUnorderedThreeExecution.value,PlayerSpecificAlgebraicThreeDraw.draw]

end Blotto.PlayerSpecificThreeDrawExecution
