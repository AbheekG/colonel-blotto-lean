import Blotto.AffineCurve

/-! Each pair of source segments contributes exactly one overlap segment to
the conditional gluing measure. No subdivision hypothesis is assumed. -/

namespace Blotto
open MeasureTheory Set

structure OverlapGluing (k h : ℕ) where
  first : SegmentLottery 3 k
  second : SegmentLottery 3 h
  firstProbe : AffineProbe 3
  secondProbe : AffineProbe 3
  d : ℝ
  d_pos : 0 < d
  first_uniform : Measure.map firstProbe.value (first.law : Measure (Allocation 3)) = uniformLaw d
  second_uniform : Measure.map secondProbe.value (second.law : Measure (Allocation 3)) = uniformLaw d
  first_P_range : ∀ i, 0 ≤ firstProbe.value (first.P i) ∧ firstProbe.value (first.P i) ≤ d
  first_Q_range : ∀ i, 0 ≤ firstProbe.value (first.Q i) ∧ firstProbe.value (first.Q i) ≤ d

namespace OverlapGluing

noncomputable def auxiliary {k h : ℕ} (G : OverlapGluing k h) : AuxiliaryGluing 3 3 k :=
  ⟨G.first, G.second.law, G.firstProbe, G.secondProbe, G.d, G.d_pos, G.first_uniform,
    G.second_uniform, G.first_P_range, G.first_Q_range⟩

noncomputable def curve {k h : ℕ} (G : OverlapGluing k h) (i : Fin k) (j : Fin h) : AffineCurve 4 :=
  pairGlueCurve G.first G.second G.firstProbe G.secondProbe i j

noncomputable def lower {k h : ℕ} (G : OverlapGluing k h) (i : Fin k) (j : Fin h) : ℝ :=
  overlapLower (G.firstProbe.value (G.first.P i)) (G.firstProbe.value (G.first.Q i))
    (G.secondProbe.value (G.second.P j)) (G.secondProbe.value (G.second.Q j))

noncomputable def upper {k h : ℕ} (G : OverlapGluing k h) (i : Fin k) (j : Fin h) : ℝ :=
  overlapUpper (G.firstProbe.value (G.first.P i)) (G.firstProbe.value (G.first.Q i))
    (G.secondProbe.value (G.second.P j)) (G.secondProbe.value (G.second.Q j))

noncomputable def density {k h : ℕ} (G : OverlapGluing k h) (i : Fin k) (j : Fin h) : ℝ :=
  G.first.conditionalWeight G.firstProbe G.d i *
    (G.second.weight j / |G.secondProbe.value (G.second.Q j) - G.secondProbe.value (G.second.P j)|)

noncomputable def weight {k h : ℕ} (G : OverlapGluing k h) (i : Fin k) (j : Fin h) : ℝ :=
  G.density i j * max (G.upper i j - G.lower i j) 0

/-- The direct rational formula for a source-pair overlap weight. -/
theorem weight_formula {k h : ℕ} (G : OverlapGluing k h) (i : Fin k) (j : Fin h) :
    G.weight i j = G.d * G.first.weight i * G.second.weight j * max (G.upper i j - G.lower i j) 0 /
      (|G.firstProbe.value (G.first.Q i) - G.firstProbe.value (G.first.P i)| *
        |G.secondProbe.value (G.second.Q j) - G.secondProbe.value (G.second.P j)|) := by
  simp only [weight, density, SegmentLottery.conditionalWeight, div_eq_mul_inv, mul_inv_rev]
  ring

theorem density_nonnegative {k h : ℕ} (G : OverlapGluing k h) (i : Fin k) (j : Fin h) : 0 ≤ G.density i j := by
  dsimp [density, SegmentLottery.conditionalWeight]
  exact mul_nonneg (div_nonneg (mul_nonneg (le_of_lt G.d_pos) (G.first.nonnegative i)) (abs_nonneg _))
    (div_nonneg (G.second.nonnegative j) (abs_nonneg _))

theorem weight_nonnegative {k h : ℕ} (G : OverlapGluing k h) (i : Fin k) (j : Fin h) : 0 ≤ G.weight i j :=
  mul_nonneg (G.density_nonnegative i j) (le_max_right _ _)

noncomputable def allocationMap {k h : ℕ} (G : OverlapGluing k h) (i : Fin k) : Allocation 3 → Allocation 4 :=
  glueAllocation ∘ G.auxiliary.pairedPoint i

theorem measurable_allocationMap {k h : ℕ} (G : OverlapGluing k h) (i : Fin k) : Measurable (G.allocationMap i) :=
  measurable_glueAllocation.comp (G.auxiliary.measurable_pairedPoint i)

/-- The exact weighted restriction of a second-source segment equals its
single pairwise overlap contribution to the four-coordinate law. -/
theorem pair_contribution {k h : ℕ} (G : OverlapGluing k h) (i : Fin k) (j : Fin h) :
    ENNReal.ofReal (G.first.conditionalWeight G.firstProbe G.d i) •
      Measure.map (G.allocationMap i)
        ((ENNReal.ofReal (G.second.weight j) • (segmentLaw (G.second.P j) (G.second.Q j) : Measure (Allocation 3))).restrict
          (G.auxiliary.cell i)) =
      ENNReal.ofReal (G.weight i j) •
        (segmentLaw ((G.curve i j).value (G.lower i j)) ((G.curve i j).value (G.upper i j)) : Measure (Allocation 4)) := by
  by_cases h0 : G.second.weight j = 0
  · simp [weight, density, h0]
  · have hnonconst : G.secondProbe.value (G.second.P j) ≠ G.secondProbe.value (G.second.Q j) :=
      fun h => h0 (G.second.constant_probe_weight_zero G.secondProbe G.d G.second_uniform j h)
    have hcoef : 0 ≤ G.first.conditionalWeight G.firstProbe G.d i := by
      dsimp [SegmentLottery.conditionalWeight]
      exact div_nonneg (mul_nonneg (le_of_lt G.d_pos) (G.first.nonnegative i)) (abs_nonneg _)
    have hI : MeasurableSet (G.first.auxiliaryInterval G.firstProbe i) := measurableSet_Icc
    rw [Measure.restrict_smul, Measure.map_smul _ (G.measurable_allocationMap i).aemeasurable]
    change ENNReal.ofReal (G.first.conditionalWeight G.firstProbe G.d i) •
      (ENNReal.ofReal (G.second.weight j) •
        Measure.map (G.allocationMap i)
          ((segmentLaw (G.second.P j) (G.second.Q j) : Measure (Allocation 3)).restrict
            (G.secondProbe.value ⁻¹' G.first.auxiliaryInterval G.firstProbe i))) = _
    rw [G.second.lift_observation_restrict G.secondProbe j hnonconst _
      (G.measurable_allocationMap i) _ hI]
    have hc : G.allocationMap i ∘ G.second.pointAt G.secondProbe j = (G.curve i j).value := by
      funext z
      dsimp [allocationMap, Function.comp_def, AuxiliaryGluing.pairedPoint, auxiliary, curve, pairGlueCurve]
      rw [G.second.pointAt_probe G.secondProbe j hnonconst]
    rw [hc, ← Measure.map_smul _ (G.curve i j).measurable.aemeasurable]
    rw [SegmentLottery.auxiliaryInterval, weighted_observation_overlap _ _ _ _ _ (G.second.nonnegative j)
      (fun h => (hnonconst h).elim), Measure.map_smul _ (G.curve i j).measurable.aemeasurable,
      smul_smul, ← ENNReal.ofReal_mul hcoef]
    exact ((G.curve i j).weighted_interval (G.lower i j) (G.upper i j) (G.density i j)
      (G.density_nonnegative i j)).symm

end OverlapGluing
end Blotto
