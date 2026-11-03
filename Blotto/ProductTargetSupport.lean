import Blotto.ProductSamplerProbability

/-! The exact target law assigns zero mass to infeasible true labels. Positive
weighted atoms decode to canonical feasible whole rows; no assumption is made
that every label in the untruncated Cartesian universe is feasible. -/

namespace Blotto
open MeasureTheory Set Filter
open scoped BigOperators Classical
namespace ProductBidTree

theorem targetRow_feasible_of_weight (tree : ProductBidTree) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ))
    (label : Fin tree.guideTree.real.trueSize) (hWeight : 0 < tree.targetWeights budget hm label) :
    Feasible (budget : ℝ) (tree.targetRow label) := by
  have hResource : tree.guideTree.real.trueFamily.resource label ≤ (budget : ℝ) := by
    by_contra hr
    simp only [targetWeights, WeightedGuideTree.feasibleTargetWeight, hr, ite_false, zero_div, lt_self_iff_false] at hWeight
  let native := label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize)
  have he := tree.resource_eq_trueFamily native
  have hLabel : native.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm = label := Fin.ext rfl
  rw [hLabel] at he
  have hq : tree.resource native ≤ budget := by exact_mod_cast (he.trans_le hResource)
  exact tree.realRow_feasible native budget hq

theorem targetLaw_supported (tree : ProductBidTree) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) : Supported (budget : ℝ) (tree.targetLaw budget hm) := by
  change ∀ᵐ row ∂mixtureMeasure (tree.targetWeights budget hm)
    (fun label => allocationPointLaw (tree.targetRow label)), Feasible (budget : ℝ) row
  apply Measure.ae_sum_iff.mpr
  intro label
  by_cases hp : 0 < tree.targetWeights budget hm label
  · apply Measure.ae_smul_measure
    change ∀ᵐ row ∂Measure.dirac (tree.targetRow label), Feasible (budget : ℝ) row
    rw [ae_dirac_eq]
    exact tree.targetRow_feasible_of_weight budget hm label hp
  · have hz : tree.targetWeights budget hm label = 0 :=
      le_antisymm (le_of_not_gt hp) (tree.targetWeights_nonnegative budget hm label)
    simp only [hz, ENNReal.ofReal_zero, zero_smul]
    simp

end ProductBidTree
end Blotto
