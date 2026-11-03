import Blotto.RealThresholdChoice
import Blotto.ParameterLaw

/-! One real uniform comparison chooses between two measurable continuations
with an independent remaining seed. The actual whole law is the exact mixture. -/

namespace Blotto.RealIndependentChoice
open MeasureTheory Set
open scoped Classical

noncomputable def sample {S α : Type*} (p : ℝ) (upper lower : S → α) (z : ℝ × S) : α :=
  RealThresholdChoice.sample p (upper z.2) (lower z.2) z.1

theorem measurable_sample {S α : Type*} [MeasurableSpace S] [MeasurableSpace α]
    (p : ℝ) (upper lower : S → α) (hUpper : Measurable upper) (hLower : Measurable lower) :
    Measurable (sample p upper lower) := by
  unfold sample RealThresholdChoice.sample
  apply Measurable.ite
  · exact measurableSet_Iic.preimage measurable_fst
  · exact hUpper.comp measurable_snd
  · exact hLower.comp measurable_snd

theorem preimage {S α : Type*} (p : ℝ) (upper lower : S → α) (A : Set α) :
    sample p upper lower ⁻¹' A = (Iic p ×ˢ (upper ⁻¹' A)) ∪ (Ioi p ×ˢ (lower ⁻¹' A)) := by
  ext z
  by_cases h : z.1 ≤ p <;> simp [sample, RealThresholdChoice.sample, h]
  intro _
  exact lt_of_not_ge h

theorem intervals_disjoint {S : Type*} (p : ℝ) (A B : Set S) : Disjoint (Iic p ×ˢ A) (Ioi p ×ˢ B) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hLe : z.1 ≤ p := hz.1
  have hLt : p < z.1 := hz'.1
  exact (not_lt_of_ge hLe) hLt

theorem unit_lower_mass (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : (unitUniform : Measure ℝ) (Iic p) = ENNReal.ofReal p := by
  have h := congrArg ENNReal.ofReal (RealThresholdChoice.unit_lower_mass p hp)
  rw [ofReal_measureReal (measure_ne_top _ _)] at h
  exact h

theorem unit_upper_mass (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : (unitUniform : Measure ℝ) (Ioi p) = ENNReal.ofReal (1 - p) := by
  have h := congrArg ENNReal.ofReal (RealThresholdChoice.unit_upper_mass p hp)
  rw [ofReal_measureReal (measure_ne_top _ _)] at h
  exact h

theorem map_product {S α : Type*} [MeasurableSpace S] [MeasurableSpace α]
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ν : ProbabilityMeasure S) (upper lower : S → α)
    (hUpper : Measurable upper) (hLower : Measurable lower) :
    Measure.map (sample p upper lower) ((unitUniform : Measure ℝ).prod (ν : Measure S)) =
      ENNReal.ofReal p • Measure.map upper (ν : Measure S) +
        ENNReal.ofReal (1 - p) • Measure.map lower (ν : Measure S) := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_sample p upper lower hUpper hLower) hA, preimage]
  rw [measure_union (intervals_disjoint p _ _) (measurableSet_Ioi.prod (hA.preimage hLower))]
  rw [Measure.prod_prod, Measure.prod_prod, unit_lower_mass p hp, unit_upper_mass p hp]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply hUpper hA, Measure.map_apply hLower hA]
  rfl

end Blotto.RealIndependentChoice
