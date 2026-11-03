import Blotto.RealCDFDistance
import Blotto.UniformInterval
import Blotto.FiniteMixture

/-! A real-RAM comparison with one independent unit-uniform input realizes
an exact binary choice. Endpoint probabilities and their zero-measure boundary
paths are included; no rational digit approximation is used. -/

namespace Blotto.RealThresholdChoice
open MeasureTheory Set
open scoped Classical BigOperators

noncomputable def sample {α : Type*} (p : ℝ) (upper lower : α) (u : ℝ) : α :=
  if u ≤ p then upper else lower

theorem measurable_sample {α : Type*} [MeasurableSpace α] (p : ℝ) (upper lower : α) :
    Measurable (sample p upper lower) := by
  unfold sample
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem sample_forBranches {α : Type*} (p : ℝ) (upper lower : α) (u : ℝ) (P : α → Prop)
    (hUpper : P upper) (hLower : P lower) : P (sample p upper lower u) := by
  unfold sample
  split
  · exact hUpper
  · exact hLower

theorem preimage {α : Type*} (p : ℝ) (upper lower : α) (A : Set α) :
    sample p upper lower ⁻¹' A =
      if upper ∈ A then (if lower ∈ A then univ else Iic p) else (if lower ∈ A then Ioi p else ∅) := by
  classical
  ext u
  by_cases hUpper : upper ∈ A <;> by_cases hLower : lower ∈ A <;>
    by_cases hU : u ≤ p <;> simp [sample, hUpper, hLower, hU]
  exact lt_of_not_ge hU

theorem unit_lower_mass (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : (unitUniform : Measure ℝ).real (Iic p) = p := by
  rw [unitUniform_closedCDF, min_eq_left hp.2, max_eq_left hp.1]

theorem unit_upper_mass (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : (unitUniform : Measure ℝ).real (Ioi p) = 1 - p := by
  have hSet : Ioi p = (Iic p)ᶜ := by ext u; simp
  rw [hSet, measureReal_compl measurableSet_Iic, unit_lower_mass p hp, probReal_univ]

noncomputable def law {α : Type*} [MeasurableSpace α] (p : ℝ) (upper lower : α) : ProbabilityMeasure α :=
  unitUniform.map (sample p upper lower)

theorem law_real_event {α : Type*} [MeasurableSpace α] (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (upper lower : α) (A : Set α) (hA : MeasurableSet A) :
    (law p upper lower : Measure α).real A =
      p * (if upper ∈ A then (1 : ℝ) else 0) + (1 - p) * (if lower ∈ A then (1 : ℝ) else 0) := by
  classical
  change (Measure.map (sample p upper lower) (unitUniform : Measure ℝ)).real A = _
  rw [map_measureReal_apply (measurable_sample p upper lower) hA, preimage]
  by_cases hu : upper ∈ A <;> by_cases hl : lower ∈ A <;>
    simp [hu, hl, unit_lower_mass p hp, unit_upper_mass p hp]

noncomputable def pointLaw {α : Type*} [MeasurableSpace α] (x : α) : ProbabilityMeasure α :=
  ⟨Measure.dirac x, inferInstance⟩

theorem law_eq_mixture {α : Type*} [MeasurableSpace α] (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (upper lower : α) :
    law p upper lower = probabilityMixture ![p, 1 - p] ![pointLaw upper, pointLaw lower]
      (by intro j; fin_cases j; exact hp.1; exact sub_nonneg.mpr hp.2) (by simp) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro A hA
  have hReal : (law p upper lower : Measure α).real A =
      (probabilityMixture ![p, 1 - p] ![pointLaw upper, pointLaw lower]
        (by intro j; fin_cases j; exact hp.1; exact sub_nonneg.mpr hp.2) (by simp) : Measure α).real A := by
    rw [law_real_event p hp upper lower A hA, probabilityMixture_real_apply _ _ _ _ _ hA]
    by_cases hu : upper ∈ A <;> by_cases hl : lower ∈ A <;>
      simp [Fin.sum_univ_succ, pointLaw, Measure.real, Measure.dirac_apply' _ hA, hu, hl]
  have h := congrArg ENNReal.ofReal hReal
  rw [ofReal_measureReal (measure_ne_top _ _), ofReal_measureReal (measure_ne_top _ _)] at h
  exact h

end Blotto.RealThresholdChoice
