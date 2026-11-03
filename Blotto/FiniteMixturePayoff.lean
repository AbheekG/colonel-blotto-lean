import Blotto.FiniteMixture

/-! Exact affine payoff identities for actual finite whole-law mixtures.
The independent-product definition and canonical half ties are retained. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

theorem probabilityMixture_integral {α : Type*} [MeasurableSpace α] {k : ℕ}
    (weight : Fin k → ℝ) (laws : Fin k → ProbabilityMeasure α)
    (hWeight : ∀ i, 0 ≤ weight i) (hSum : ∑ i, weight i = 1)
    (f : α → ℝ) (hIntegrable : ∀ i, Integrable f (laws i : Measure α)) :
    (∫ row, f row ∂(probabilityMixture weight laws hWeight hSum : Measure α)) =
      ∑ i, weight i * ∫ row, f row ∂(laws i : Measure α) := by
  change (∫ row, f row ∂Measure.sum
    (fun i => ENNReal.ofReal (weight i) • (laws i : Measure α))) = _
  rw [Measure.sum_fintype,integral_finsetSum_measure]
  · simp only [integral_smul_measure,ENNReal.toReal_ofReal (hWeight _),smul_eq_mul]
  · intro i _
    exact (hIntegrable i).smul_measure ENNReal.ofReal_ne_top

theorem expected_probabilityMixture_left {n k : ℕ} (values : Values n)
    (weight : Fin k → ℝ) (laws : Fin k → Mixed n)
    (hWeight : ∀ i, 0 ≤ weight i) (hSum : ∑ i, weight i = 1) (opponent : Mixed n) :
    expected values (probabilityMixture weight laws hWeight hSum) opponent =
      ∑ i, weight i * expected values (laws i) opponent := by
  simp only [expected_iterated]
  exact probabilityMixture_integral weight laws hWeight hSum _
    (fun i => integrable_purePayoff values (laws i) opponent)

theorem expected_probabilityMixture_right {n k : ℕ} (values : Values n)
    (weight : Fin k → ℝ) (laws : Fin k → Mixed n)
    (hWeight : ∀ i, 0 ≤ weight i) (hSum : ∑ i, weight i = 1) (own : Mixed n) :
    expected values own (probabilityMixture weight laws hWeight hSum) =
      ∑ i, weight i * expected values own (laws i) := by
  have hLeft := expected_probabilityMixture_left values weight laws hWeight hSum own
  have hConstant := expected_constant_sum values own (probabilityMixture weight laws hWeight hSum)
  have hEach : ∀ i, expected values (laws i) own = 1 - expected values own (laws i) := by
    intro i
    have h := expected_constant_sum values own (laws i)
    linarith
  simp_rw [hEach] at hLeft
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib,hSum] at hLeft
  linarith

end Blotto
