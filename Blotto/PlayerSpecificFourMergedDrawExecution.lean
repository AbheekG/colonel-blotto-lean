import Blotto.PlayerSpecificFourMergedInputSourceCost
import Blotto.PlayerSpecificThreeDrawSourceCost

/-! The measured small uniform draw prepares its merged child once, draws
the complete child once, and proportionally splits the first coordinate. -/
namespace Blotto.PlayerSpecificFourMergedDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin (8*H+K) → Bool) : FixedArrayTable 4 Data×ℕ :=
  let p := PlayerSpecificFourMergedInputExecution.run model root a
  let y := PlayerSpecificThreeDrawExecution.run model root p.1.child H K bits
  let result := PlayerSpecificSplitFirstTwoExecution.run model root p.1.first p.1.second y.1
  (result.1,p.2+y.2+result.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin (8*H+K) → Bool) :
    (run model root a H K bits).1=
      PlayerSpecificAlgebraicFourMergedDraw.draw model root a H K bits := by
  simp only [run,PlayerSpecificFourMergedInputExecution.value,
    PlayerSpecificThreeDrawExecution.value,PlayerSpecificSplitFirstTwoExecution.value,
    PlayerSpecificAlgebraicFourMergedDraw.draw]

end Blotto.PlayerSpecificFourMergedDrawExecution
