import Blotto.PlayerSpecificMidpointCost
import Blotto.PlayerSpecificAlgebraicMidpointCoin

/-! The measured native Bernoulli choice computes its midpoint once and
performs one exact retained-root comparison. Equality still chooses false. -/
namespace Blotto.PlayerSpecificAlgebraicCoinExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (probability : Data) (midpoint : ℚ) (H : ℕ) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run [probability,[midpoint]] [H,1]

def run (model : RationalCostModel) (root : Candidate) (probability : Data) (H : ℕ) (bits : Fin H → Bool) : Bool×ℕ :=
  let midpoint:=PlayerSpecificMidpointExecution.run model H bits
  let comparison:=PlayerSpecificAlgebraicComparisonExecution.run model root probability [midpoint.1]
  (!comparison.1,midpoint.2+comparison.2+price model (frame probability midpoint.1 H))

theorem value (model : RationalCostModel) (root : Candidate) (probability : Data) (H : ℕ) (bits : Fin H → Bool) :
    (run model root probability H bits).1=PlayerSpecificAlgebraicMidpointCoin.run model root probability H bits := by
  simp only [run,PlayerSpecificMidpointExecution.value,PlayerSpecificAlgebraicComparisonExecution.value,
    PlayerSpecificAlgebraicMidpointCoin.run]

end Blotto.PlayerSpecificAlgebraicCoinExecution
