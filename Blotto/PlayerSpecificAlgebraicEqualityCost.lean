import Blotto.PlayerSpecificAlgebraicEqualityExecution

/-! Complete exact equality has a quadratic fixed-degree source price
in its actual input coefficient height. No selected-root oracle is needed. -/
namespace Blotto.PlayerSpecificAlgebraicEqualityCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 200001000
def polynomialCoefficient : ℕ := coefficient*(PlayerSpecificAlgebraicComparisonCost.widthCoefficient^2+
  PlayerSpecificAlgebraicComparisonCost.widthCoefficient)

theorem cost (model : RationalCostModel) (m a b : Data) (H : ℕ)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4) (ha : Reduced m a) (hb : Reduced m b)
    (hmH : HasHeight m H) (haH : HasHeight a H) (hbH : HasHeight b H) (hH : 1≤H) :
    (PlayerSpecificAlgebraicEqualityExecution.run model m a b).2≤
      coefficient*model.rat (PlayerSpecificAlgebraicComparisonExecution.width H) := by
  let difference:=PlayerSpecificFieldCombination.run true m a b
  let W:=PlayerSpecificAlgebraicComparisonExecution.width H
  have hal : a.length≤3 := by have h:=ha.2; omega
  have hbl : b.length≤3 := by have h:=hb.2; omega
  have hdiffred : Reduced m difference.1 := PlayerSpecificFieldCombination.reduced true m a b hm hm0
  have hdiffLen : difference.1.length≤3 := by have h:=hdiffred.2; omega
  have hdiff : HasHeight difference.1 (2*H+1) := by
    change HasHeight (PlayerSpecificFieldCombination.run true m a b).1 (2*H+1)
    rw [PlayerSpecificFieldCombination.value]
    change HasHeight (PlayerSpecificAlgebraicField.minus m a b) (2*H+1)
    simpa only [two_mul] using PlayerSpecificShortReduction.minus_height m a b hm hm0 ha hb H H haH hbH
  have hinput:=inputHeight_le hdiff
  have hinputMul:=Nat.mul_le_mul_right (1+2*(2*H+1)) hdiffLen
  have hlarge:=PlayerSpecificAlgebraicInitialPrimitiveCost.large (2*H+1)
  have hW : 32≤W := by change 32≤PlayerSpecificAlgebraicInitialPrimitiveCost.width (2*H+1); omega
  have hHW : 1+2*(2*H+1)≤W := by change _≤PlayerSpecificAlgebraicInitialPrimitiveCost.width (2*H+1); omega
  have hzeroWidth : 2*PlayerSpecificRationalMagnitude.inputHeight difference.1+32≤W := by
    change _≤PlayerSpecificAlgebraicInitialPrimitiveCost.width (2*H+1)
    omega
  have hcombined:=(PlayerSpecificFieldCombinationCost.run_cost model true m a b hm hm0 hml H hmH haH hbH hH hal hbl).trans
    (Nat.mul_le_mul_left _ (model.monotone (PlayerSpecificAlgebraicExpressionPrimitiveCost.combination_width H)))
  have hzero:=(PlayerSpecificAlgebraicZeroExecution.source_cost model difference.1 hdiffLen).trans
    (Nat.mul_le_mul_left _ (model.monotone hzeroWidth))
  have hframe:=PlayerSpecificAlgebraicCallerFrame.cost model [m,a,b,difference.1] [1,3] (2*H+1) W
    (by intro row hrow; simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow; rcases hrow with hrow|hrow|hrow|hrow
        · rw [hrow]; exact mono hmH (by omega)
        · rw [hrow]; exact mono haH (by omega)
        · rw [hrow]; exact mono hbH (by omega)
        · rw [hrow]; exact hdiff)
    (by intro row hrow; simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow; rcases hrow with hrow|hrow|hrow|hrow <;> rw [hrow] <;> omega)
    (by intro word hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with hw|hw <;> rw [hw] <;>
      exact (control_width _).trans (by omega)) hHW hW
  simp only [List.length_cons,List.length_nil] at hframe
  change price model difference.2+(PlayerSpecificAlgebraicZeroExecution.run model difference.1).2+
    price model (PlayerSpecificAlgebraicEqualityExecution.frame m a b difference.1)≤coefficient*model.rat W
  change price model difference.2≤200000000*model.rat W at hcombined
  change _≤100*model.rat W at hzero
  change price model (PlayerSpecificAlgebraicEqualityExecution.frame m a b difference.1)≤270*model.rat W at hframe
  unfold coefficient
  omega

theorem polynomial_cost (m a b : Data) (H : ℕ)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4) (ha : Reduced m a) (hb : Reduced m b)
    (hmH : HasHeight m H) (haH : HasHeight a H) (hbH : HasHeight b H) (hH : 1≤H) :
    (PlayerSpecificAlgebraicEqualityExecution.run RationalCostModel.schoolbook m a b).2≤polynomialCoefficient*(H+1)^2 := by
  have hc:=cost RationalCostModel.schoolbook m a b H hm hm0 hml ha hb hmH haH hbH hH
  rw [PlayerSpecificAlgebraicComparisonCost.width_linear] at hc
  exact hc.trans (PlayerSpecificAlgebraicInverseContract.quadratic_profile coefficient _ (H+1) (by omega))

end Blotto.PlayerSpecificAlgebraicEqualityCost
