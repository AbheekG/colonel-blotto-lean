import Blotto.FiniteMixture

/-! Measurability of finite segment families and actual averaging of parameter-
dependent measures. These lemmas will be used to assemble conditional samplers. -/

namespace Blotto
open MeasureTheory Set Filter
open scoped BigOperators

/-- A jointly measurable sampling map gives a measurable family of laws. -/
theorem measurable_parameter_map {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure β) [SFinite μ]
    (f : α → β → γ) (hf : Measurable (Function.uncurry f)) :
    Measurable (fun a => Measure.map (f a) μ) := by
  apply Measure.measurable_measure.mpr
  intro A hA
  have hm := measurable_measure_prodMk_left (ν := μ) (hA.preimage hf)
  have he : (fun a => (Measure.map (f a) μ) A) =
      (fun a => μ (Prod.mk a ⁻¹' (Function.uncurry f ⁻¹' A))) := by
    funext a
    rw [Measure.map_apply hf.of_uncurry_left hA]
    rfl
  rw [he]
  exact hm

theorem measurable_affineUniform_family {α : Type*} [MeasurableSpace α]
    {a b : α → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun s => (affineUniform (a s) (b s) : Measure ℝ)) := by
  apply measurable_parameter_map (unitUniform : Measure ℝ)
  exact ((measurable_const.sub measurable_snd).mul (ha.comp measurable_fst)).add
    (measurable_snd.mul (hb.comp measurable_fst))

theorem measurable_segmentLaw_family {α : Type*} [MeasurableSpace α] {n : ℕ}
    {P Q : α → Allocation n} (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (fun s => (segmentLaw (P s) (Q s) : Measure (Allocation n))) := by
  apply measurable_parameter_map (unitUniform : Measure ℝ)
  apply Measurable.of_eval
  intro j
  exact ((measurable_const.sub measurable_snd).mul
      ((measurable_pi_apply j).comp (hP.comp measurable_fst))).add
    (measurable_snd.mul ((measurable_pi_apply j).comp (hQ.comp measurable_fst)))

/-- Exact measurable push-forwards commute with averaging a measurable family. -/
theorem map_bind_family {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure α) (law : α → Measure β)
    (hlaw : Measurable law) (f : β → γ) (hf : Measurable f) :
    Measure.map f (μ.bind law) = μ.bind (fun a => Measure.map f (law a)) := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hf hA, Measure.bind_apply (hA.preimage hf) hlaw.aemeasurable,
    Measure.bind_apply hA]
  · apply lintegral_congr
    intro a
    exact (Measure.map_apply hf hA).symm
  · exact (Measure.measurable_map f hf).comp hlaw |>.aemeasurable

/-- Measurable real weights may multiply a parameter-dependent measure. -/
theorem measurable_weighted_law {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {weight : α → ℝ} {law : α → Measure β}
    (hw : Measurable weight) (hlaw : Measurable law) :
    Measurable (fun a => ENNReal.ofReal (weight a) • law a) := by
  apply Measure.measurable_measure.mpr
  intro A hA
  simp only [Measure.smul_apply, smul_eq_mul]
  exact hw.ennreal_ofReal.mul ((Measure.measurable_coe hA).comp hlaw)

/-- Almost-sure support is preserved by actual measurable conditional averaging. -/
theorem bind_ae_family {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (law : α → Measure β) (hlaw : Measurable law) {p : β → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ a ∂μ, ∀ᵐ x ∂law a, p x) :
    ∀ᵐ x ∂μ.bind law, p x := by
  have hneg : MeasurableSet {x | ¬p x} := hp.compl
  rw [ae_iff, Measure.bind_apply hneg hlaw.aemeasurable]
  calc
    _ = ∫⁻ a, (0 : ENNReal) ∂μ :=
      lintegral_congr_ae (h.mono fun _ ha => ae_iff.mp ha)
    _ = 0 := lintegral_zero

noncomputable def averagedLaw {α : Type*} [MeasurableSpace α] {n : ℕ}
    (μ : ProbabilityMeasure α) (law : α → Mixed n)
    (hlaw : Measurable (fun a => (law a : Measure (Allocation n)))) : Mixed n :=
  ⟨(μ : Measure α).bind (fun a => (law a : Measure (Allocation n))),
    isProbabilityMeasure_bind hlaw.aemeasurable
      (Eventually.of_forall fun a => (law a).property)⟩

theorem averagedLaw_fullBudget {α : Type*} [MeasurableSpace α] {n : ℕ}
    (μ : ProbabilityMeasure α) (law : α → Mixed n)
    (hlaw : Measurable (fun a => (law a : Measure (Allocation n)))) {B : ℝ}
    (h : ∀ᵐ a ∂(μ : Measure α), ∀ᵐ x ∂(law a : Measure (Allocation n)), FullBudget B x) :
    ∀ᵐ x ∂(averagedLaw μ law hlaw : Measure (Allocation n)), FullBudget B x :=
  bind_ae_family _ _ hlaw (measurable_fullBudget B) h

theorem averagedLaw_marginal {α : Type*} [MeasurableSpace α] {n : ℕ}
    (μ : ProbabilityMeasure α) (law : α → Mixed n)
    (hlaw : Measurable (fun a => (law a : Measure (Allocation n)))) (j : Fin n) :
    (marginal (averagedLaw μ law hlaw) j : Measure ℝ) =
      (μ : Measure α).bind (fun a => (marginal (law a) j : Measure ℝ)) :=
  map_bind_family _ _ hlaw (fun x => x j) (measurable_pi_apply j)

theorem averagedLaw_marginal_constant {α : Type*} [MeasurableSpace α] {n : ℕ}
    (μ : ProbabilityMeasure α) (law : α → Mixed n)
    (hlaw : Measurable (fun a => (law a : Measure (Allocation n)))) (j : Fin n) (ρ : Measure ℝ)
    (h : (fun a => (marginal (law a) j : Measure ℝ)) =ᵐ[(μ : Measure α)] (fun _ => ρ)) :
    (marginal (averagedLaw μ law hlaw) j : Measure ℝ) = ρ := by
  rw [averagedLaw_marginal, Measure.bind_congr_right h, Measure.bind_const, measure_univ, one_smul]

end Blotto
