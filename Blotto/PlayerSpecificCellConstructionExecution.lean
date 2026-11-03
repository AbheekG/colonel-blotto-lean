import Blotto.PlayerSpecificSuffixCost

/-! Actual priced rational-cell construction. Each field ratio and sweep
move is computed once, then reused by the emitted cell and next frame.
Complete suffix-input and returned-cell lists are copied and priced. -/
namespace Blotto.PlayerSpecificCellConstructionExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificSweep PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def frame (s : State ℚ) (lower : ℚ) (xs : PlayerSpecificSuffixExecution.Rows) (result : List Cell) : Trace :=
  PlayerSpecificSweepExecution.copyState s++copyRow [lower]++PlayerSpecificSuffixExecution.copyRows xs++
    PlayerSpecificRecognitionScanExecution.copyCells result++[.control xs.length,.control result.length]
def run (model : RationalCostModel) (s : State ℚ) (lower : ℚ) : PlayerSpecificSuffixExecution.Rows → List Cell×ℕ
  | [] =>
    let result:=[⟨s,lower,none,0⟩]
    (result,price model (frame s lower [] result))
  | x::xs =>
    let ratio:=scalar .divide x.1.1 x.1.2
    let moved:=PlayerSpecificSweepExecution.move s x.1.1 x.1.2
    let tail:=run model moved.1 ratio.1 xs
    let result:=⟨s,lower,some ratio.1,x.2⟩::tail.1
    (result,price model ratio.2+price model moved.2+tail.2+price model (frame s lower (x::xs) result))

theorem value (model : RationalCostModel) (s : State ℚ) (lower : ℚ) (xs : PlayerSpecificSuffixExecution.Rows) :
    (run model s lower xs).1=build s lower xs := by
  induction xs generalizing s lower with
  | nil => rfl
  | cons x xs ih => simp only [run,PlayerSpecificSweepExecution.move_value,scalar_value,Arithmetic.apply,ih,build]

theorem length (model : RationalCostModel) (s : State ℚ) (lower : ℚ) (xs : PlayerSpecificSuffixExecution.Rows) :
    (run model s lower xs).1.length=xs.length+1 := by
  rw [value]
  exact count s lower xs

end Blotto.PlayerSpecificCellConstructionExecution
