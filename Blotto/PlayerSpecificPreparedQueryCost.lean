import Blotto.PlayerSpecificEndpointTraceCost

/-! Endpoint query costs for the actually prepared squarefree/Sturm rows.
The row coefficient/length bounds are derived from the original input.
Dyadic traversal queries consequently use only linear-width operands. -/
namespace Blotto.PlayerSpecificPreparedQueryCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalMagnitude
open PlayerSpecificSquarefreeHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def queryHeight (p : Data) (T : ℕ) : ℕ := certificateHeight (inputHeight p)+T+1
def queryWidth (p : Data) (T : ℕ) : ℕ := 22*queryHeight p T+48

theorem input_pos (p : Data) : 1 ≤ inputHeight p := by unfold inputHeight; omega

theorem prepared_bounds (p : Data) (prepared : PlayerSpecificIsolationState.Prepared p) (hlen : p.length≤4) :
    (∀ row∈prepared.sequence,HasHeight row (certificateHeight (inputHeight p)) ∧ row.length≤4) ∧ prepared.sequence.length≤5 := by
  rw [prepared.correct]
  exact ⟨PlayerSpecificSturmHeights.rows_bounds p _ (input_height p) (input_pos p) hlen,
    PlayerSpecificSturmHeights.rows_length p _ (input_height p) (input_pos p) hlen⟩

theorem endpoint_cost (model : RationalCostModel) (p : Data) (prepared : PlayerSpecificIsolationState.Prepared p)
    (hlen : p.length≤4) (x : ℚ) (T : ℕ) (hx : RationalHeight x T) :
    price model (PlayerSpecificEndpointExecution.endpoint prepared x).2≤4000*model.rat (queryWidth p T) := by
  have h := prepared_bounds p prepared hlen
  apply PlayerSpecificEndpointTraceCost.cubic_query_cost model prepared.sequence x (queryHeight p T)
  · intro row hr
    have hh := h.1 row hr
    exact ⟨mono hh.1 (by unfold queryHeight; omega),hh.2⟩
  · exact hx.mono (by unfold queryHeight; omega)
  · exact h.2

theorem endpoint_count (p : Data) (prepared : PlayerSpecificIsolationState.Prepared p)
    (hlen : p.length≤4) (x : ℚ) : (PlayerSpecificEndpointExecution.endpoint prepared x).1≤5 := by
  have hc := PlayerSpecificVariationExecution.count_le_length (PlayerSpecificEndpointExecution.evalRows prepared.sequence x).1
  rw [PlayerSpecificEndpointExecution.evalRows_length] at hc
  exact hc.trans (prepared_bounds p prepared hlen).2

def linearWidthCoefficient : ℕ :=
  22*(certificateConstant+PlayerSpecificIsolationDepthHeight.linearConstant+7)+48

theorem traversal_query_width (p : Data) (hlen : p.length≤4) (k : ℕ)
    (hk : k≤PlayerSpecificRootIsolation.depth p) :
    queryWidth p (2*inputHeight p+k+4)≤linearWidthCoefficient*(inputHeight p+1) := by
  have hd := PlayerSpecificIsolationDepthHeight.depth_linear p hlen
  have hc := certificate_linear (inputHeight p)
  unfold queryWidth queryHeight linearWidthCoefficient
  nlinarith

theorem traversal_endpoint_cost (model : RationalCostModel) (p : Data) (prepared : PlayerSpecificIsolationState.Prepared p)
    (hlen : p.length≤4) (node : PlayerSpecificIsolationState.Interval) (k : ℕ)
    (hk : k≤PlayerSpecificRootIsolation.depth p) (hv : PlayerSpecificIsolationState.Valid prepared node)
    (hg : PlayerSpecificDyadicEndpoints.Grid node k)
    (hb : PlayerSpecificDyadicEndpoints.Bounded node (PlayerSpecificRootMagnitude.rootBound p:ℚ)) :
    price model (PlayerSpecificEndpointExecution.endpoint prepared node.lo).2≤
      4000*model.rat (linearWidthCoefficient*(inputHeight p+1)) ∧
    price model (PlayerSpecificEndpointExecution.endpoint prepared node.hi).2≤
      4000*model.rat (linearWidthCoefficient*(inputHeight p+1)) := by
  have h := PlayerSpecificDyadicEndpoints.endpoint_height p prepared node k hv hg hb
  have hw := traversal_query_width p hlen k hk
  have hm := Nat.mul_le_mul_left 4000 (model.monotone hw)
  exact ⟨(endpoint_cost model p prepared hlen node.lo _ h.1).trans hm,
    (endpoint_cost model p prepared hlen node.hi _ h.2).trans hm⟩

end Blotto.PlayerSpecificPreparedQueryCost
