import Blotto.PlayerSpecificTerminalCoreInputSourceCost
import Blotto.PlayerSpecificAlgebraicTerminalCoreExecution

/-! One reached-state grouping feeds the measured terminal core input
and exactly one measured four-case draw. -/
namespace Blotto.PlayerSpecificTerminalCoreMeasuredExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    FixedArrayTable 4 Data × ℕ :=
  let input := PlayerSpecificTerminalCoreInputExecution.run p s B
  let drawn := PlayerSpecificTerminalCoreDrawExecution.run p.parameters input.1 H K bits
  (drawn.1,input.2+drawn.2+price RationalCostModel.schoolbook [.control 1])

theorem value {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    (run p s B H K bits).1 = PlayerSpecificAlgebraicTerminalCoreExecution.run p s B H K bits := by
  simp only [run,PlayerSpecificTerminalCoreInputExecution.value,
    PlayerSpecificTerminalCoreDrawExecution.value,PlayerSpecificAlgebraicTerminalCoreExecution.run]

end Blotto.PlayerSpecificTerminalCoreMeasuredExecution
