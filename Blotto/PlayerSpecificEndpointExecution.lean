import Blotto.PlayerSpecificVariationTraceCost

/-! Actual cached-row endpoint evaluation and sign-variation counting,
returning numerical values and source traces together. -/
namespace Blotto.PlayerSpecificEndpointExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def evalRows : List Data → ℚ → Data×Trace
  | [],x => ([],[.control 0,.copy x])
  | p::rows,x =>
    let head := PlayerSpecificDenseExecution.evaluate p x
    let tail := evalRows rows x
    PlayerSpecificDenseExecution.finish (head.1::tail.1)
      ([.control (rows.length+1)]++head.2++tail.2)

theorem evalRows_value (rows : List Data) (x : ℚ) :
    (evalRows rows x).1=rows.map (fun p => evaluate p x) := by
  induction rows with
  | nil => rfl
  | cons p rows ih => simp only [evalRows,PlayerSpecificDenseExecution.finish,
      PlayerSpecificDenseExecution.evaluate_value,ih,List.map_cons]

theorem evalRows_length (rows : List Data) (x : ℚ) : (evalRows rows x).1.length=rows.length := by
  rw [evalRows_value,List.length_map]

theorem evalRows_height (rows : List Data) (x : ℚ) (H N : ℕ)
    (h : ∀ p∈rows,HasHeight p H ∧ p.length≤N) (hx : RationalHeight x H) :
    HasHeight (evalRows rows x).1 ((2*H+1)*N+1) := by
  intro q hq
  rw [evalRows_value] at hq
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
  have hr := h p hp
  apply (evaluate_height hr.1 hx).mono
  nlinarith

theorem evalRows_trace_length (rows : List Data) (x : ℚ) (N M : ℕ)
    (h : ∀ p∈rows,p.length≤N) (hlen : rows.length≤M) :
    (evalRows rows x).2.length≤(11*N+M+8)*(rows.length+1) := by
  induction rows with
  | nil => simp only [evalRows,List.length_cons,List.length_nil]; nlinarith
  | cons p rows ih =>
    have hp := h p List.mem_cons_self
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem p hq)) (by simp only [List.length_cons] at hlen; omega)
    simp only [evalRows,PlayerSpecificDenseExecution.finish,List.length_append,copyRow_length,
      List.length_cons,List.length_nil,PlayerSpecificDenseExecution.evaluate_trace_length,evalRows_length]
    simp only [List.length_cons] at hlen
    nlinarith

def run (rows : List Data) (x : ℚ) : ℕ×Trace :=
  let values := evalRows rows x
  let counted := PlayerSpecificVariationExecution.run values.1
  (counted.1,values.2++counted.2++[.control rows.length,.control counted.1])

theorem value (rows : List Data) (x : ℚ) :
    (run rows x).1=PlayerSpecificSturmSequence.variations rows x := by
  simp only [run,PlayerSpecificVariationExecution.value,evalRows_value,PlayerSpecificSturmSequence.variations]

def endpoint {p : Data} (prepared : PlayerSpecificIsolationState.Prepared p) (x : ℚ) : ℕ×Trace :=
  run prepared.sequence x

theorem endpoint_value {p : Data} (prepared : PlayerSpecificIsolationState.Prepared p) (x : ℚ) :
    (endpoint prepared x).1=PlayerSpecificIsolationState.variations prepared x := value prepared.sequence x

end Blotto.PlayerSpecificEndpointExecution
