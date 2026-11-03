import Blotto.PlayerSpecificSignPreparationCost

/-! Both defining-polynomial endpoint queries are executed from the cached
rows before selected-root refinement. The retained endpoints receive the
new actual variation values for their defining polynomial. -/
namespace Blotto.PlayerSpecificSignRetagExecution
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1000000

def run {p : Data} (prepared : Prepared p) (node : Interval) : Interval×Trace :=
  let low:=PlayerSpecificEndpointExecution.endpoint prepared node.lo
  let high:=PlayerSpecificEndpointExecution.endpoint prepared node.hi
  let result:Interval:=⟨node.lo,node.hi,low.1,high.1⟩
  (result,copyRow [node.lo,node.hi]++low.2++high.2++PlayerSpecificSplitExecution.copyInterval result++[.control 2])

theorem value {p : Data} (prepared : Prepared p) (node : Interval) :
    (run prepared node).1=PlayerSpecificSignEnclosure.retag prepared node := by
  simp only [run,PlayerSpecificEndpointExecution.endpoint_value,PlayerSpecificSignEnclosure.retag,initial]

end Blotto.PlayerSpecificSignRetagExecution
