import Blotto.RealCDFDistance

/-! Coupled output maps which agree outside a failure event differ in every
event probability by at most that event's probability. This is the precise
bridge needed when bounded sampling emits a feasible fallback on exhaustion. -/

namespace Blotto
open MeasureTheory Set

theorem coupled_event_error {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : ProbabilityMeasure α) (f g : α → β) (hf : Measurable f) (hg : Measurable g)
    (failure : Set α) (hag : ∀ x ∉ failure, f x = g x) (A : Set β) (hA : MeasurableSet A) :
    |(ρ.map f : Measure β).real A - (ρ.map g : Measure β).real A| ≤ (ρ : Measure α).real failure := by
  change |(Measure.map f (ρ : Measure α)).real A - (Measure.map g (ρ : Measure α)).real A| ≤ _
  rw [map_measureReal_apply hf hA, map_measureReal_apply hg hA]
  have hfg : f ⁻¹' A ⊆ g ⁻¹' A ∪ failure := by
    intro x hx
    by_cases he : x ∈ failure
    · exact Or.inr he
    · exact Or.inl (by simpa only [mem_preimage, hag x he] using hx)
  have hgf : g ⁻¹' A ⊆ f ⁻¹' A ∪ failure := by
    intro x hx
    by_cases he : x ∈ failure
    · exact Or.inr he
    · exact Or.inl (by simpa only [mem_preimage, hag x he] using hx)
  have h1 := (measureReal_mono (μ := (ρ : Measure α)) hfg).trans (measureReal_union_le _ _)
  have h2 := (measureReal_mono (μ := (ρ : Measure α)) hgf).trans (measureReal_union_le _ _)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem coupled_scalar_CDF_error {α : Type*} [MeasurableSpace α] (ρ : ProbabilityMeasure α)
    (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g) (failure : Set α)
    (hag : ∀ x ∉ failure, f x = g x) :
    RealCDFClose (ρ.map f) (ρ.map g) ((ρ : Measure α).real failure) :=
  fun z => coupled_event_error ρ f g hf hg failure hag (Iic z) measurableSet_Iic

theorem coupled_allocation_CDF_error {α : Type*} [MeasurableSpace α] {n : ℕ}
    (ρ : ProbabilityMeasure α) (f g : α → Allocation n) (hf : Measurable f) (hg : Measurable g)
    (failure : Set α) (hag : ∀ x ∉ failure, f x = g x) :
    CDFClose (ρ.map f) (ρ.map g) ((ρ : Measure α).real failure) := by
  intro j z
  have hc := coupled_event_error ρ (fun x => f x j) (fun x => g x j)
    ((measurable_pi_apply j).comp hf) ((measurable_pi_apply j).comp hg) failure
    (fun x hx => congrFun (hag x hx) j) (Iic z) measurableSet_Iic
  change |(Measure.map (fun x : Allocation n => x j) (Measure.map f (ρ : Measure α))).real (Iic z) -
    (Measure.map (fun x : Allocation n => x j) (Measure.map g (ρ : Measure α))).real (Iic z)| ≤ _
  rw [Measure.map_map (measurable_pi_apply j) hf, Measure.map_map (measurable_pi_apply j) hg]
  exact hc

end Blotto
