import Blotto.PlayerSpecificBreakpointTestCost

/-! Complete separately tested rational breakpoint, retaining an actual
degree-one root representation and pricing both optional outcomes. -/
namespace Blotto.PlayerSpecificBreakpointExecution
open PlayerSpecificRationalCells PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def frame (c : Cell) (b : ℚ) (result : Option Candidate) : Trace :=
  PlayerSpecificCellTestConstruction.copyCell c++copyRow [b]++
    PlayerSpecificCandidateScanExecution.copyOption result++[.control (if result.isSome then 1 else 0)]

def run (c : Cell) (b : ℚ) : Option Candidate×Trace :=
  match c.upper with
  | none => (none,frame c b none)
  | some q =>
    let tested:=PlayerSpecificBreakpointTestExecution.run c b q
    let constructed:=PlayerSpecificBreakpointConstruction.run q
    let result:=if tested.1 then some constructed.1 else none
    (result,tested.2++constructed.2++frame c b result)

theorem value (c : Cell) (b : ℚ) (hb : b≠0) : (run c b).1=PlayerSpecificRationalBreakpoint.run c b := by
  cases hu : c.upper with
  | none => simp only [run,PlayerSpecificRationalBreakpoint.run,hu]
  | some q =>
    simp only [run,PlayerSpecificRationalBreakpoint.run,hu,PlayerSpecificBreakpointConstruction.value]
    simp only [PlayerSpecificBreakpointTestExecution.value c b q hb]

end Blotto.PlayerSpecificBreakpointExecution
