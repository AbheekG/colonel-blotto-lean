import Blotto.RealSegmentSampler

/-! A single fixed vector of independent real uniforms feeds segment
selection and interpolation. Read/callback labels exclude body arithmetic
and physical container costs. -/

namespace Blotto.SegmentLottery
open MeasureTheory

noncomputable def realSampleFlat {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k)
    (seed : Fin ((k - 1) + 1) → ℝ) : Allocation n :=
  l.realSample fallback (Fin.tail seed, seed 0)

theorem realSampleFlat_refines {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k)
    (seed : Fin ((k - 1) + 1) → ℝ) :
    l.realSampleFlat fallback seed =
      l.point (realCategorical l.weight l.nonnegative fallback (Fin.tail seed)) (seed 0) :=
  l.realSample_refines fallback _

theorem realSampleFlat_measurable {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k) :
    Measurable (l.realSampleFlat fallback) :=
  (l.realSample_measurable fallback).comp (measurable_swap.comp (RealUniformInputs.measurable_split (k - 1)))

theorem realSampleFlat_law {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k) :
    Measure.map (l.realSampleFlat fallback)
      (RealUniformInputs.law ((k - 1) + 1) : Measure (Fin ((k - 1) + 1) → ℝ)) =
      (l.law : Measure (Allocation n)) := by
  rw [RealUniformInputs.map_law_succ _ _ (l.realSampleFlat_measurable fallback)]
  have hComp : l.realSampleFlat fallback ∘ RealUniformInputs.join = l.realSample fallback ∘ Prod.swap := by
    funext z
    simp [realSampleFlat, realSample, RealUniformInputs.join]
  rw [hComp, ← Measure.map_map (l.realSample_measurable fallback) measurable_swap,
    Measure.prod_swap]
  exact l.realSample_law fallback

theorem realSampleFlat_fullBudget {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k) {B : ℝ}
    (hP : ∀ i, FullBudget B (l.P i)) (hQ : ∀ i, FullBudget B (l.Q i))
    (seed : Fin ((k - 1) + 1) → ℝ) (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) :
    FullBudget B (l.realSampleFlat fallback seed) :=
  l.realSample_fullBudget fallback hP hQ _ ht

theorem realSampleFlat_read_labels {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k)
    (seed : Fin ((k - 1) + 1) → ℝ) :
    ((realCategoricalMachine fallback).run (k - 1)
      (.remaining (realWeightTable l.weight l.nonnegative)) (Fin.tail seed)).2 + 1 ≤ k := by
  have hRead := (realCategoricalMachine fallback).run_reads_rank (k - 1)
    (.remaining (realWeightTable l.weight l.nonnegative)) (Fin.tail seed)
  have hRank : (realCategoricalMachine fallback).rank
      (.remaining (realWeightTable l.weight l.nonnegative)) = k - 1 := by
    simp [realCategoricalMachine, realCategoricalRank, realWeightTable, RealWeightList.prepare]
  rw [hRank] at hRead
  have hPos : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) fallback.isLt
  omega

end Blotto.SegmentLottery
