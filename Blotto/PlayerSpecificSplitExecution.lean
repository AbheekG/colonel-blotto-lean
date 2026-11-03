import Blotto.PlayerSpecificPreparedQueryCost

/-! Traced cached bisection split: one rational midpoint, one endpoint query
and two child records reusing its variation value. -/
namespace Blotto.PlayerSpecificSplitExecution
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 3500000

def copyInterval (node : Interval) : Trace :=
  [.copy node.lo,.copy node.hi,.control node.loValue,.control node.hiValue,.control node.count]

def run {p : Data} (prepared : Prepared p) (node : Interval) : (Interval×Interval)×Trace :=
  let summed := scalar .add node.lo node.hi
  let middle := scalar .divide summed.1 2
  let counted := PlayerSpecificEndpointExecution.endpoint prepared middle.1
  let left : Interval := ⟨node.lo,middle.1,node.loValue,counted.1⟩
  let right : Interval := ⟨middle.1,node.hi,counted.1,node.hiValue⟩
  ((left,right),[.control prepared.sequence.length,.control node.loValue,.control node.hiValue]++
    summed.2++middle.2++counted.2++copyInterval left++copyInterval right)

theorem value {p : Data} (prepared : Prepared p) (node : Interval) : (run prepared node).1=split prepared node := by
  simp only [run,scalar,Arithmetic.apply,PlayerSpecificEndpointExecution.endpoint_value,split,Interval.midpoint]

theorem copyInterval_length (node : Interval) : (copyInterval node).length=5 := rfl

theorem query_trace_length (p : Data) (prepared : Prepared p) (hlen : p.length≤4) (x : ℚ) :
    (PlayerSpecificEndpointExecution.endpoint prepared x).2.length≤1064 := by
  have hb := PlayerSpecificPreparedQueryCost.prepared_bounds p prepared hlen
  have h := PlayerSpecificEndpointTraceCost.run_trace_length prepared.sequence x 4 5 (fun row hr => (hb.1 row hr).2) hb.2
  norm_num only [Nat.reduceAdd,Nat.reduceMul,Nat.reducePow] at h
  exact h

theorem trace_length (p : Data) (prepared : Prepared p) (hlen : p.length≤4) (node : Interval) :
    (run prepared node).2.length≤1087 := by
  have h := query_trace_length p prepared hlen ((scalar .divide (scalar .add node.lo node.hi).1 2).1)
  simp only [run,List.length_append,List.length_cons,List.length_nil,scalar_length,copyInterval_length]
  omega

theorem variation_bound (p : Data) (prepared : Prepared p) (hlen : p.length≤4) (x : ℚ) :
    variations prepared x≤5 := by
  rw [← PlayerSpecificEndpointExecution.endpoint_value]
  exact PlayerSpecificPreparedQueryCost.endpoint_count p prepared hlen x

theorem stored_counts (p : Data) (prepared : Prepared p) (hlen : p.length≤4) (node : Interval) (h : Valid prepared node) :
    node.loValue≤5 ∧ node.hiValue≤5 ∧ node.count≤5 := by
  have hlo : node.loValue≤5 := by rw [h.2.1]; exact variation_bound p prepared hlen node.lo
  have hhi : node.hiValue≤5 := by rw [h.2.2]; exact variation_bound p prepared hlen node.hi
  exact ⟨hlo,hhi,(Nat.sub_le _ _).trans hlo⟩

end Blotto.PlayerSpecificSplitExecution
