import Blotto.PlayerSpecificRationalOutputExecution
import Blotto.PlayerSpecificFiniteDrawMeasuredSourceCost
import Blotto.PlayerSpecificRationalFiniteDraw

/-! One measured finite rational draw executes the complete algebraic
packet, then floors each original-coordinate output. The source return is
the native rational finite draw on every packet. -/
namespace Blotto.PlayerSpecificRationalFiniteMeasuredExecution
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (B : ℚ) (player : Bool) (H K P : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicFiniteDraw.bitCount N H K) → Bool) :
    FixedArrayTable N ℚ×ℕ :=
  let drawn:=PlayerSpecificFiniteDrawMeasuredExecution.run p B player H K bits
  let rounded:=PlayerSpecificRationalOutputExecution.run p.parameters.root drawn.1 P
  (rounded.1,drawn.2+rounded.2+price RationalCostModel.schoolbook [.control P])

theorem value {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (B : ℚ) (player : Bool) (H K P : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicFiniteDraw.bitCount N H K) → Bool) :
    (run p B player H K P bits).1=PlayerSpecificRationalFiniteDraw.draw p B player H K P bits := by
  simp only [run,PlayerSpecificFiniteDrawMeasuredExecution.value,
    PlayerSpecificRationalOutputExecution.value,PlayerSpecificRationalFiniteDraw.draw]

end Blotto.PlayerSpecificRationalFiniteMeasuredExecution
