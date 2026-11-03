import Blotto.PlayerSpecificTerminalLeafEmissionPolynomial
import Blotto.PlayerSpecificFiniteResourceEntryCost
import Blotto.PlayerSpecificAlgebraicFiniteDrawContract

/-! Actual finite packet execution from the prepared algebraic input:
priced disjoint bit slices, one measured resource entry, and the measured
original-coordinate terminal leaf on its returned state. -/
namespace Blotto.PlayerSpecificFiniteDrawMeasuredExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (B : ℚ) (player : Bool) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicFiniteDraw.bitCount N H K) → Bool) :
    FixedArrayTable N Data × ℕ :=
  let model := RationalCostModel.schoolbook
  let R := (N-1)*H
  let F := PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K
  let first := PlayerSpecificBitSliceExecution.run model (R+F) 0 R (by omega) bits
  let second := PlayerSpecificBitSliceExecution.run model (R+F) R F (Nat.le_refl _) bits
  let resource := PlayerSpecificFiniteResourceEntryExecution.draw p player H first.1
  let leaf := PlayerSpecificTerminalLeafMeasuredExecution.run p resource.1.1
    (if player then 1 else B) H K second.1
  (leaf.1,first.2+second.2+resource.2+leaf.2+price model [.control 1])

theorem value {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (B : ℚ) (player : Bool) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicFiniteDraw.bitCount N H K) → Bool) :
    (run p B player H K bits).1 = PlayerSpecificAlgebraicFiniteDraw.draw p B player H K bits := by
  let R := (N-1)*H
  let F := PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K
  let model := RationalCostModel.schoolbook
  have hfirst : (PlayerSpecificBitSliceExecution.run model (R+F) 0 R (by omega) bits).1 =
      PlayerSpecificAlgebraicFiniteDraw.resourceBits N H K bits := by
    exact PlayerSpecificBitSliceExecution.first_value model R F bits
  have hsecond : (PlayerSpecificBitSliceExecution.run model (R+F) R F (Nat.le_refl _) bits).1 =
      PlayerSpecificAlgebraicFiniteDraw.terminalBits N H K bits := by
    exact PlayerSpecificBitSliceExecution.second_value model R F bits
  simp only [run]
  rw [hfirst,hsecond,PlayerSpecificFiniteResourceEntryExecution.value,
    PlayerSpecificTerminalLeafMeasuredExecution.value]
  rfl

end Blotto.PlayerSpecificFiniteDrawMeasuredExecution
