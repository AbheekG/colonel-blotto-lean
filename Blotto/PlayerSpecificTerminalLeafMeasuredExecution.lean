import Blotto.PlayerSpecificTerminalLeafEmissionSourceCost

/-! One cached terminal grouping feeds the measured core input and draw,
then the measured original-coordinate emitter. No grouping or core output
is supplied as an input to this reached-state program. -/
namespace Blotto.PlayerSpecificTerminalLeafMeasuredExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    FixedArrayTable N Data × ℕ :=
  let grouped := PlayerSpecificTerminalPreparationExecution.run RationalCostModel.schoolbook p s B
  let input := PlayerSpecificTerminalCoreInputExecution.fromPrepared p s B grouped.1
  let drawn := PlayerSpecificTerminalCoreDrawExecution.run p.parameters input.1 H K bits
  let emitted := PlayerSpecificTerminalLeafEmissionExecution.fromCore RationalCostModel.schoolbook
    p.parameters.root (fun j => (p.rows.read j).length)
    grouped.1.groups grouped.1.fractional drawn.1
  (emitted.1,grouped.2+input.2+drawn.2+emitted.2+
    price RationalCostModel.schoolbook [.control 1])

theorem value {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    (run p s B H K bits).1 = PlayerSpecificAlgebraicTerminalLeafExecution.run p s B H K bits := by
  simp only [run,PlayerSpecificTerminalLeafEmissionExecution.fromCore_value,
    PlayerSpecificTerminalCoreDrawExecution.value,
    PlayerSpecificTerminalCoreInputExecution.fromPrepared_value,
    PlayerSpecificTerminalPreparationExecution.value,
    PlayerSpecificAlgebraicTerminalLeafExecution.run]

end Blotto.PlayerSpecificTerminalLeafMeasuredExecution
