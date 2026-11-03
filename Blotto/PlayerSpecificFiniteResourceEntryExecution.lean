import Blotto.PlayerSpecificResourceBlockPolynomial

/-! The complete measured resource entry constructs its actual state
and fair blocks once, executes the measured adaptive loop and prices the
returned state/caller frame. Its return is exactly the native draw. -/
namespace Blotto.PlayerSpecificFiniteResourceEntryExecution
set_option autoImplicit false
set_option maxHeartbeats 2500000

def draw {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (player : Bool) (H : ℕ)
    (bits : Fin ((N-1)*H) → Bool) : (PlayerSpecificAlgebraicResourceState.State N×ℕ)×ℕ :=
  let initial:=PlayerSpecificAlgebraicStateExecution.start RationalCostModel.schoolbook p player
  let blocks:=PlayerSpecificResourceBlockExecution.blocks RationalCostModel.schoolbook (N-1) H bits
  let result:=PlayerSpecificFiniteResourceExecution.run RationalCostModel.schoolbook p H (N-1) initial.1 blocks.1
  (result.1,initial.2+blocks.2+result.2+
    PlayerSpecificFiniteResourceExecution.frame RationalCostModel.schoolbook p H (N-1) blocks.1.length result.1.2 result.1.1)

theorem value {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (player : Bool) (H : ℕ)
    (bits : Fin ((N-1)*H) → Bool) :
    (draw p player H bits).1=PlayerSpecificFiniteResourceLoop.draw p player H bits := by
  simp only [draw,PlayerSpecificAlgebraicStateExecution.start_value,PlayerSpecificResourceBlockExecution.blocks_value,
    PlayerSpecificFiniteResourceExecution.value,PlayerSpecificFiniteResourceLoop.draw]

end Blotto.PlayerSpecificFiniteResourceEntryExecution
