import Blotto.PlayerSpecificPolynomialSignCost

/-! Complete exact sign of every original four-entry polynomial at a
retained algebraic root, with original-input polynomial source time. -/
namespace Blotto.PlayerSpecificPolynomialSignContract
open SignType PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificIsolationState
open PlayerSpecificSturmVariations PlayerSpecificPolynomialSignBudget PlayerSpecificPolynomialSignCost
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_contract (model : RationalCostModel) (m p : Data) (node : Interval) (hm : Normalized m)
    (hirr : Irreducible (semantics m)) (hml : m.length≤4) (hpl : p.length≤4) (hv : node.lo<node.hi)
    (x : ℝ) (hu : PlayerSpecificSelectedRefinement.Unique m node x) :
    let result:=PlayerSpecificPolynomialSignExecution.run model m p node
    result.1=sign (realEvaluate p x) ∧
      result.2≤workCoefficient*(inputHeight m p node+1)*model.rat (width (inputHeight m p node)) := by
  have hm0 : m≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  exact ⟨PlayerSpecificPolynomialSignExecution.correct model m p node hm hirr hv x hu,run_cost model m p node hm hm0 hml hpl hv⟩

theorem polynomial_cost (m p : Data) (node : Interval) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hpl : p.length≤4) (hv : node.lo<node.hi) :
    (PlayerSpecificPolynomialSignExecution.run RationalCostModel.schoolbook m p node).2≤
      polynomialCoefficient*(inputHeight m p node+1)^3 := by
  have hc:=run_cost RationalCostModel.schoolbook m p node hm hm0 hml hpl hv
  change (PlayerSpecificPolynomialSignExecution.run RationalCostModel.schoolbook m p node).2≤
    workCoefficient*(inputHeight m p node+1)*
      ((widthCoefficient*(inputHeight m p node+1))*(widthCoefficient*(inputHeight m p node+1))+
        widthCoefficient*(inputHeight m p node+1)) at hc
  exact hc.trans (PlayerSpecificRootContract.schoolbook_profile _ _ _ (by omega))

end Blotto.PlayerSpecificPolynomialSignContract
