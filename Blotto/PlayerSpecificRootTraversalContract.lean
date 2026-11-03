import Blotto.PlayerSpecificForestTraceCost

/-! One actual original-input return carries the complete functional root
isolation, linear endpoint heights and polynomial traversal-source price.
The source price for polynomial/integer preprocessing remains outstanding. -/
namespace Blotto.PlayerSpecificRootTraversalContract
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem actual_contract (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    let result := PlayerSpecificForestTraceCost.traversal p
    result.1.length≤3 ∧
    (∀ leaf∈result.1,∃! x : ℝ,PlayerSpecificSturmVariations.realEvaluate p x=0 ∧ leaf.Contains x) ∧
    (∀ x : ℝ,PlayerSpecificSturmVariations.realEvaluate p x=0 → ∃ leaf∈result.1,leaf.Contains x) ∧
    (∀ leaf∈result.1,
      RationalHeight leaf.lo ((PlayerSpecificIsolationDepthHeight.linearConstant+6)*(inputHeight p+1)) ∧
      RationalHeight leaf.hi ((PlayerSpecificIsolationDepthHeight.linearConstant+6)*(inputHeight p+1))) ∧
    PlayerSpecificRationalTrace.price model result.2≤
      (30600*PlayerSpecificIsolationDepthHeight.linearConstant+5100)*(inputHeight p+1)*
        model.rat (PlayerSpecificTraversalPrice.widthCoefficient*(inputHeight p+1)) := by
  have hv := PlayerSpecificForestTraceCost.traversal_value p
  refine ⟨?_,?_,?_,?_,PlayerSpecificForestTraceCost.traversal_cost model p hp hlen⟩
  · rw [hv]
    exact PlayerSpecificRootIsolation.length_le_three p hp hlen
  · rw [hv]
    exact PlayerSpecificRootIsolation.unique_roots p hp hlen
  · intro x hx
    rw [hv]
    exact PlayerSpecificRootIsolation.covers p hp x hx
  · rw [hv]
    exact fun leaf hl => PlayerSpecificDyadicEndpoints.returned_height_linear p hlen leaf hl

end Blotto.PlayerSpecificRootTraversalContract
