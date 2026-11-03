import Blotto.OverlapContribution

/-! The full conditional allocation law is the finite sum of pairwise overlap
segments. This identity establishes the representation before normalization. -/

namespace Blotto.OverlapGluing
open MeasureTheory Set
open scoped BigOperators

theorem allocation_measure {k h : ℕ} (G : OverlapGluing k h) :
    (G.auxiliary.allocationLaw : Measure (Allocation 4)) =
      Measure.sum (fun i => Measure.sum (fun j => ENNReal.ofReal (G.weight i j) •
        (segmentLaw ((G.curve i j).value (G.lower i j)) ((G.curve i j).value (G.upper i j)) : Measure (Allocation 4)))) := by
  change Measure.map glueAllocation G.auxiliary.rawLaw = _
  rw [AuxiliaryGluing.rawLaw, Measure.map_sum measurable_glueAllocation.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul _ measurable_glueAllocation.aemeasurable,
    Measure.map_map measurable_glueAllocation (G.auxiliary.measurable_pairedPoint i)]
  change ENNReal.ofReal (G.first.conditionalWeight G.firstProbe G.d i) •
    Measure.map (G.allocationMap i) ((G.second.law : Measure (Allocation 3)).restrict (G.auxiliary.cell i)) = _
  rw [G.second.law_measure, Measure.restrict_sum _ (G.auxiliary.measurable_cell i),
    Measure.map_sum (G.measurable_allocationMap i).aemeasurable]
  simp only [Measure.sum_fintype, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact G.pair_contribution i j

/-- All real overlap weights normalize, as an identity inherited from the
already normalized actual conditional joint law. -/
theorem weights_mass {k h : ℕ} (G : OverlapGluing k h) : ∑ i, ∑ j, G.weight i j = 1 := by
  have he : (G.auxiliary.allocationLaw : Measure (Allocation 4)) univ = 1 := measure_univ
  rw [G.allocation_measure] at he
  simp only [Measure.sum_fintype, Measure.finsetSum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at he
  have hN : ENNReal.ofReal (∑ i, ∑ j, G.weight i j) = ∑ i, ∑ j, ENNReal.ofReal (G.weight i j) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => G.weight_nonnegative i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.ofReal_sum_of_nonneg (fun j _ => G.weight_nonnegative i j)
  rw [← hN] at he
  have hsum : 0 ≤ ∑ i, ∑ j, G.weight i j := Finset.sum_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => G.weight_nonnegative i j))
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal hsum, ENNReal.toReal_one] using hr

end Blotto.OverlapGluing
