import Blotto.ProductSamplerProbability

/-! Probability-measure event identities equal the verified kernel means.
Zero-weight infeasible target labels contribute no measure mass; support is
proved on positive-weight labels without strengthening the target domain. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators Classical
namespace ProductBidTree

theorem targetLaw_event (tree : ProductBidTree) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ))
    (event : Set (Allocation tree.fields)) (hEvent : MeasurableSet event) :
    (tree.targetLaw budget hm : Measure (Allocation tree.fields)).real event =
      (tree.guideTree.targetKernel budget hm).mean (fun label => if tree.targetRow label ∈ event then 1 else 0) := by
  unfold targetLaw
  rw [probabilityMixture_real_apply _ _ _ _ _ hEvent]
  change (∑ label, tree.targetWeights budget hm label * (Measure.dirac (tree.targetRow label)).real event) = _
  apply Finset.sum_congr rfl
  intro label _
  change tree.targetWeights budget hm label * (Measure.dirac (tree.targetRow label)).real event =
    tree.targetWeights budget hm label * (if tree.targetRow label ∈ event then 1 else 0)
  rw [Measure.real, Measure.dirac_apply' _ hEvent]
  by_cases h : tree.targetRow label ∈ event <;> simp [h]

theorem scheduledLaw_event (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ) (fallback : Fin tree.labels)
    (event : Set (Allocation tree.fields)) (hEvent : MeasurableSet event) :
    (tree.scheduledLaw hc budget hm E fallback : Measure (Allocation tree.fields)).real event =
      (fairBitKernel (tree.guideTree.scheduledBitBudget E)).mean
        (fun bits => if (fun field => (tree.scheduledRow hc budget hm E fallback bits field : ℝ)) ∈ event then 1 else 0) := by
  change (Measure.map (fun bits field => (tree.scheduledRow hc budget hm E fallback bits field : ℝ))
    (fairBitLaw (tree.guideTree.scheduledBitBudget E) : Measure (Fin (tree.guideTree.scheduledBitBudget E) → Bool))).real event = _
  rw [map_measureReal_apply (measurable_of_countable _) hEvent]
  change _ = ∫ bits, _ ∂(fairBitLaw (tree.guideTree.scheduledBitBudget E) :
    Measure (Fin (tree.guideTree.scheduledBitBudget E) → Bool))
  have he : (fun bits : Fin (tree.guideTree.scheduledBitBudget E) → Bool =>
      if (fun field => (tree.scheduledRow hc budget hm E fallback bits field : ℝ)) ∈ event then (1 : ℝ) else 0) =
      ((fun bits field => (tree.scheduledRow hc budget hm E fallback bits field : ℝ)) ⁻¹' event).indicator (fun _ => 1) := by
    funext bits
    rfl
  rw [he, integral_indicator_const _ (hEvent.preimage (measurable_of_countable _)), smul_eq_mul, mul_one]

theorem scheduledLaw_event_error (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ) (fallback : Fin tree.labels)
    (event : Set (Allocation tree.fields)) (hEvent : MeasurableSet event) :
    |(tree.scheduledLaw hc budget hm E fallback : Measure (Allocation tree.fields)).real event -
      (tree.targetLaw budget hm : Measure (Allocation tree.fields)).real event| ≤ 1 / (2 : ℝ) ^ E := by
  rw [tree.scheduledLaw_event hc budget hm E fallback event hEvent, tree.targetLaw_event budget hm event hEvent]
  exact tree.scheduledRow_event_error hc budget hm E fallback event

theorem scheduledLaw_CDFClose (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ) (fallback : Fin tree.labels) :
    CDFClose (tree.scheduledLaw hc budget hm E fallback) (tree.targetLaw budget hm) (1 / (2 : ℝ) ^ E) := by
  intro field threshold
  unfold closedCDF marginal
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [map_measureReal_apply (measurable_pi_apply field) measurableSet_Iic,
    map_measureReal_apply (measurable_pi_apply field) measurableSet_Iic]
  exact tree.scheduledLaw_event_error hc budget hm E fallback
    {row | row field ≤ threshold} (measurableSet_le (measurable_pi_apply field) measurable_const)

end ProductBidTree
end Blotto
