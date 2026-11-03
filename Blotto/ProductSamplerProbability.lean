import Blotto.ProductEpsilonSampler
import Blotto.CDF
import Blotto.FiniteMixtureOrder

/-! Actual bounded whole-row samplers and exact feasible product targets as
probability measures. CDF and support contracts now use the canonical Mixed
interfaces, retaining within-player coordinate dependence. -/

namespace Blotto
open MeasureTheory Set Filter
open scoped BigOperators Classical
namespace ProductBidTree

noncomputable def targetWeights (tree : ProductBidTree) (budget : ℚ)
    (_hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ))
    (label : Fin tree.guideTree.real.trueSize) : ℝ :=
  tree.guideTree.real.feasibleTargetWeight (budget : ℝ) label /
    tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)

theorem targetWeights_nonnegative (tree : ProductBidTree) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (label : Fin tree.guideTree.real.trueSize) :
    0 ≤ tree.targetWeights budget hm label := by
  apply div_nonneg _ hm.le
  unfold WeightedGuideTree.feasibleTargetWeight
  split_ifs
  · exact tree.guideTree.real.trueFamily.mass_nonnegative label
  · exact le_rfl

theorem targetWeights_sum (tree : ProductBidTree) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) :
    (∑ label, tree.targetWeights budget hm label) = 1 := by
  unfold targetWeights
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  change tree.guideTree.real.trueFamily.prefixMass (budget : ℝ) *
    (tree.guideTree.real.trueFamily.prefixMass (budget : ℝ))⁻¹ = 1
  exact mul_inv_cancel₀ (ne_of_gt hm)

noncomputable def allocationPointLaw {n : ℕ} (row : Allocation n) : Mixed n :=
  ⟨Measure.dirac row, inferInstance⟩

noncomputable def targetLaw (tree : ProductBidTree) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) : Mixed tree.fields :=
  probabilityMixture (tree.targetWeights budget hm) (fun label => allocationPointLaw (tree.targetRow label))
    (tree.targetWeights_nonnegative budget hm) (tree.targetWeights_sum budget hm)

noncomputable def scheduledLaw (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ) (fallback : Fin tree.labels) : Mixed tree.fields :=
  (fairBitLaw (tree.guideTree.scheduledBitBudget E)).map
    (fun bits field => (tree.scheduledRow hc budget hm E fallback bits field : ℝ))

noncomputable def epsilonLaw (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (fallback : Fin tree.labels) : Mixed tree.fields :=
  (fairBitLaw (tree.guideTree.epsilonBitBudget epsilon)).map
    (fun bits field => (tree.epsilonRow hc budget hm epsilon fallback bits field : ℝ))

theorem feasible_measurable {n : ℕ} (budget : ℝ) : MeasurableSet {row : Allocation n | Feasible budget row} := by
  have hCoords : MeasurableSet {row : Allocation n | ∀ j : Fin n, 0 ≤ row j} := by
    have he : {row : Allocation n | ∀ j : Fin n, 0 ≤ row j} =
        ⋂ j : Fin n, {row : Allocation n | 0 ≤ row j} := by ext row; simp
    rw [he]
    exact MeasurableSet.iInter (fun j => measurableSet_le measurable_const (measurable_pi_apply j))
  have hSum : MeasurableSet {row : Allocation n | (∑ j, row j) ≤ budget} :=
    measurableSet_le (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)) measurable_const
  exact hCoords.inter hSum

theorem scheduledLaw_supported (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ)
    (fallback : Fin tree.labels) (hf : tree.resource fallback ≤ budget) :
    Supported (budget : ℝ) (tree.scheduledLaw hc budget hm E fallback) := by
  change ∀ᵐ row ∂Measure.map (fun bits field => (tree.scheduledRow hc budget hm E fallback bits field : ℝ))
    (fairBitLaw (tree.guideTree.scheduledBitBudget E) : Measure (Fin (tree.guideTree.scheduledBitBudget E) → Bool)),
      Feasible (budget : ℝ) row
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (feasible_measurable (budget : ℝ))]
  exact Eventually.of_forall (tree.scheduledRow_feasible hc budget hm E fallback hf)

theorem epsilonLaw_supported (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ)
    (fallback : Fin tree.labels) (hf : tree.resource fallback ≤ budget) :
    Supported (budget : ℝ) (tree.epsilonLaw hc budget hm epsilon fallback) :=
  tree.scheduledLaw_supported hc budget hm _ fallback hf

end ProductBidTree
end Blotto
