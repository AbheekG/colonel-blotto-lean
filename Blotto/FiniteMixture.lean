import Blotto.Segments

/-! A finite lottery of probability laws with explicit nonnegative real masses.
Whole-law support and exact measurable push-forwards are preserved. -/

namespace Blotto

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable def mixtureMeasure {α : Type*} [MeasurableSpace α] {k : ℕ}
    (weight : Fin k → ℝ) (law : Fin k → ProbabilityMeasure α) : Measure α :=
  Measure.sum fun i => ENNReal.ofReal (weight i) • (law i : Measure α)

theorem mixtureMeasure_mass {α : Type*} [MeasurableSpace α] {k : ℕ}
    (weight : Fin k → ℝ) (law : Fin k → ProbabilityMeasure α) :
    mixtureMeasure weight law univ = ∑ i, ENNReal.ofReal (weight i) := by
  simp [mixtureMeasure]

noncomputable def probabilityMixture {α : Type*} [MeasurableSpace α] {k : ℕ}
    (weight : Fin k → ℝ) (law : Fin k → ProbabilityMeasure α)
    (hw : ∀ i, 0 ≤ weight i) (hs : ∑ i, weight i = 1) : ProbabilityMeasure α :=
  ⟨mixtureMeasure weight law, by
    constructor
    rw [mixtureMeasure_mass, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hs]
    norm_num⟩

theorem mixtureMeasure_ae {α : Type*} [MeasurableSpace α] {k : ℕ}
    (weight : Fin k → ℝ) (law : Fin k → ProbabilityMeasure α) {p : α → Prop}
    (h : ∀ i, ∀ᵐ x ∂(law i : Measure α), p x) :
    ∀ᵐ x ∂mixtureMeasure weight law, p x := by
  apply Measure.ae_sum_iff.mpr
  intro i
  exact Measure.ae_smul_measure (h i) (ENNReal.ofReal (weight i))

theorem probabilityMixture_ae {α : Type*} [MeasurableSpace α] {k : ℕ}
    (weight : Fin k → ℝ) (law : Fin k → ProbabilityMeasure α)
    (hw : ∀ i, 0 ≤ weight i) (hs : ∑ i, weight i = 1) {p : α → Prop}
    (h : ∀ i, ∀ᵐ x ∂(law i : Measure α), p x) :
    ∀ᵐ x ∂(probabilityMixture weight law hw hs : Measure α), p x :=
  mixtureMeasure_ae weight law h

theorem mixtureMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {k : ℕ} (weight : Fin k → ℝ) (law : Fin k → ProbabilityMeasure α)
    (f : α → β) (hf : Measurable f) :
    Measure.map f (mixtureMeasure weight law) =
      Measure.sum fun i => ENNReal.ofReal (weight i) • Measure.map f (law i : Measure α) := by
  rw [mixtureMeasure, Measure.map_sum hf.aemeasurable]
  congr 1
  funext i
  exact Measure.map_smul _ hf.aemeasurable

theorem probabilityMixture_supported {n k : ℕ} (B : ℝ) (weight : Fin k → ℝ)
    (law : Fin k → Mixed n) (hw : ∀ i, 0 ≤ weight i) (hs : ∑ i, weight i = 1)
    (h : ∀ i, Supported B (law i)) :
    Supported B (probabilityMixture weight law hw hs) :=
  probabilityMixture_ae weight law hw hs h

theorem probabilityMixture_marginal {n k : ℕ} (weight : Fin k → ℝ)
    (law : Fin k → Mixed n) (hw : ∀ i, 0 ≤ weight i) (hs : ∑ i, weight i = 1)
    (j : Fin n) :
    (marginal (probabilityMixture weight law hw hs) j : Measure ℝ) =
      Measure.sum fun i => ENNReal.ofReal (weight i) • (marginal (law i) j : Measure ℝ) :=
  mixtureMeasure_map weight law (fun x => x j) (measurable_pi_apply j)

end Blotto
