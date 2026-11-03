import Blotto.PlayerSpecificSignRetagExecution

/-! Actual cached single-path refinement. Every split, cached row, interval
record, branch/fuel word and returned interval is included in its price. -/
namespace Blotto.PlayerSpecificSelectedExecution
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def frame {p : Data} (prepared : Prepared p) (fuel : ℕ) (node result : Interval) : Trace :=
  PlayerSpecificSturmExecution.copyRows prepared.sequence++
    PlayerSpecificSplitExecution.copyInterval node++PlayerSpecificSplitExecution.copyInterval result++
      [.control fuel,.control node.count,.control 1]

def run {p : Data} (model : RationalCostModel) (prepared : Prepared p) : ℕ → Interval → Interval×ℕ
  | 0,node => (node,price model (frame prepared 0 node node))
  | fuel+1,node =>
    let parts:=PlayerSpecificSplitExecution.run prepared node
    let chosen:=if 0<parts.1.1.count then parts.1.1 else parts.1.2
    let rest:=run model prepared fuel chosen
    (rest.1,price model parts.2+rest.2+price model (frame prepared (fuel+1) node rest.1))

theorem value {p : Data} (model : RationalCostModel) (prepared : Prepared p) (fuel : ℕ) (node : Interval) :
    (run model prepared fuel node).1=PlayerSpecificSelectedRefinement.run prepared fuel node := by
  induction fuel generalizing node with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,ih,PlayerSpecificSplitExecution.value,PlayerSpecificSelectedRefinement.run,
      PlayerSpecificSelectedRefinement.step]

end Blotto.PlayerSpecificSelectedExecution
