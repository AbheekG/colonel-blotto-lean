import Blotto.PlayerSpecificAlgebraicInitialVectorCost

/-! The actual priced vector return simultaneously satisfies every
initial coupling constraint and the original-input polynomial resources.
No field, inverse, intermediate-height or aggregate-cost oracle is supplied. -/
namespace Blotto.PlayerSpecificAlgebraicInitialVectorContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificSturmVariations PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicInitialVectorBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem actual_contract {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let prepared:=PlayerSpecificAlgebraicInitialVectorExecution.run RationalCostModel.schoolbook i r
    prepared.2≤PlayerSpecificAlgebraicInitialVectorCost.polynomialCoefficient*(N+1)*size N (inputSize i)^3 ∧
      ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
        Reduced r.root.polynomial prepared.1.inverseScale ∧
        (∀ j,Reduced r.root.polynomial (prepared.1.rows.read j).length ∧
          Reduced r.root.polynomial (prepared.1.rows.read j).initialA ∧ Reduced r.root.polynomial (prepared.1.rows.read j).initialB) ∧
        (∀ j,(0<realEvaluate (prepared.1.rows.read j).length x ∧ realEvaluate (prepared.1.rows.read j).length x≤(i.budget:ℝ)) ∧
          (0≤realEvaluate (prepared.1.rows.read j).initialA x ∧ realEvaluate (prepared.1.rows.read j).initialA x≤realEvaluate (prepared.1.rows.read j).length x) ∧
          (0≤realEvaluate (prepared.1.rows.read j).initialB x ∧ realEvaluate (prepared.1.rows.read j).initialB x≤realEvaluate (prepared.1.rows.read j).length x)) ∧
        (∑ j,realEvaluate (prepared.1.rows.read j).initialA x)=2 ∧
        (∑ j,realEvaluate (prepared.1.rows.read j).initialB x)=2*(i.budget:ℝ) := by
  refine ⟨PlayerSpecificAlgebraicInitialVectorCost.polynomial_cost i r hr,?_⟩
  rw [PlayerSpecificAlgebraicInitialVectorExecution.value]
  exact PlayerSpecificAlgebraicInitialContract.actual_coupling_input i r hr

theorem output_heights {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let prepared:=(PlayerSpecificAlgebraicInitialVectorExecution.run RationalCostModel.schoolbook i r).1
    HasHeight prepared.inverseScale (PlayerSpecificAlgebraicHeightEnvelope.step (PlayerSpecificAlgebraicInitialInputSizes.base N (inputSize i))) ∧
      ∀ j,HasHeight (prepared.rows.read j).length (PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i)) ∧
        HasHeight (prepared.rows.read j).initialA (PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i)) ∧
        HasHeight (prepared.rows.read j).initialB (PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i)) := by
  rw [PlayerSpecificAlgebraicInitialVectorExecution.value]
  exact PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr

end Blotto.PlayerSpecificAlgebraicInitialVectorContract
