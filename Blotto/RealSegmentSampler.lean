import Blotto.RealCategoricalLaw
import Blotto.SegmentLottery
import Blotto.RealSegmentPointProgram

/-! Exact segment draws use a cached-mass categorical controller and one
independent unit-uniform interpolation parameter. The whole-vector law is
the existing segment lottery; the tree is only a semantic proof interface. -/

namespace Blotto.SegmentLottery
open MeasureTheory Set
open scoped BigOperators Classical

theorem measurable_point {n k : ℕ} (l : SegmentLottery n k) :
    Measurable (fun z : Fin k × ℝ => l.point z.1 z.2) := by
  apply Measurable.of_eval
  intro j
  change Measurable (fun z : Fin k × ℝ => (1 - z.2) * l.P z.1 j + z.2 * l.Q z.1 j)
  exact ((measurable_const.sub measurable_snd).mul
    ((measurable_of_countable (fun i => l.P i j)).comp measurable_fst)).add
    (measurable_snd.mul ((measurable_of_countable (fun i => l.Q i j)).comp measurable_fst))

noncomputable def realInputLaw (k : ℕ) : ProbabilityMeasure ((Fin (k - 1) → ℝ) × ℝ) :=
  RealUniformInputs.productLaw (RealUniformInputs.law (k - 1)) unitUniform

noncomputable def realSample {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k)
    (seed : (Fin (k - 1) → ℝ) × ℝ) : Allocation n :=
  let slot := realCategorical l.weight l.nonnegative fallback seed.1
  (RealSegmentPointProgram.output (l.P slot) (l.Q slot) seed.2).read

theorem realSample_refines {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k)
    (seed : (Fin (k - 1) → ℝ) × ℝ) :
    l.realSample fallback seed = l.point (realCategorical l.weight l.nonnegative fallback seed.1) seed.2 := by
  unfold realSample
  rw [RealSegmentPointProgram.output_refines]
  rfl

theorem realSample_measurable {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k) :
    Measurable (l.realSample fallback) := by
  rw [show l.realSample fallback = fun seed =>
    l.point (realCategorical l.weight l.nonnegative fallback seed.1) seed.2
    from funext (l.realSample_refines fallback)]
  exact l.measurable_point.comp ((realCategorical_measurable l.weight l.nonnegative fallback).prodMap measurable_id)

theorem realSample_fullBudget {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k) {B : ℝ}
    (hP : ∀ i, FullBudget B (l.P i)) (hQ : ∀ i, FullBudget B (l.Q i))
    (seed : (Fin (k - 1) → ℝ) × ℝ) (ht : 0 ≤ seed.2 ∧ seed.2 ≤ 1) :
    FullBudget B (l.realSample fallback seed) := by
  rw [l.realSample_refines]
  exact l.point_fullBudget hP hQ _ ht

theorem point_index_uniform_law {n k : ℕ} (l : SegmentLottery n k) :
    Measure.map (fun z : Fin k × ℝ => l.point z.1 z.2)
      ((probabilityMixture l.weight (fun i => RealThresholdChoice.pointLaw i)
        l.nonnegative l.mass : Measure (Fin k)).prod (unitUniform : Measure ℝ)) =
      (l.law : Measure (Allocation n)) := by
  change Measure.map _ ((Measure.sum fun i => ENNReal.ofReal (l.weight i) • Measure.dirac i).prod _) = _
  rw [Measure.prod_sum_left, Measure.map_sum l.measurable_point.aemeasurable]
  rw [l.law_measure]
  congr 1
  funext i
  rw [Measure.prod_smul_left, Measure.map_smul _ l.measurable_point.aemeasurable,
    Measure.dirac_prod, Measure.map_map l.measurable_point measurable_prodMk_left]
  rfl

theorem realSample_law {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k) :
    Measure.map (l.realSample fallback) (realInputLaw k : Measure ((Fin (k - 1) → ℝ) × ℝ)) =
      (l.law : Measure (Allocation n)) := by
  rw [show l.realSample fallback = fun seed =>
    l.point (realCategorical l.weight l.nonnegative fallback seed.1) seed.2
    from funext (l.realSample_refines fallback)]
  have hChoice := realCategorical_measurable l.weight l.nonnegative fallback
  have hProduct := Measure.map_prod_map (RealUniformInputs.law (k - 1) : Measure (Fin (k - 1) → ℝ))
    (unitUniform : Measure ℝ) hChoice measurable_id
  rw [realCategorical_law l.weight l.nonnegative l.mass fallback, Measure.map_id] at hProduct
  rw [← l.point_index_uniform_law, hProduct, Measure.map_map l.measurable_point (hChoice.prodMap measurable_id)]
  rfl

end Blotto.SegmentLottery
