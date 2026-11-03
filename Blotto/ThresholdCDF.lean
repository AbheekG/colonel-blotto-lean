import Blotto.RealCDFDistance

/-! A shared-support threshold identity transports Kolmogorov distance
through a nonlinear sampling map. The event identities are required on every
point of the common support; no continuity or absence of atoms is assumed. -/

namespace Blotto
open MeasureTheory Set

namespace RealCDFClose

theorem threshold_map {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ)
    (f : ℝ → ℝ) (hf : Measurable f) (E : Set ℝ)
    (hρ : ∀ᵐ x ∂(ρ : Measure ℝ), x ∈ E) (hσ : ∀ᵐ x ∂(σ : Measure ℝ), x ∈ E)
    (ht : ∀ z, ∃ q : ℝ, ∀ x ∈ E, f x ≤ z ↔ x ≤ q) :
    RealCDFClose (ρ.map f) (σ.map f) δ := by
  intro z
  rcases ht z with ⟨q, hq⟩
  have heρ : f ⁻¹' Iic z =ᵐ[(ρ : Measure ℝ)] Iic q :=
    hρ.mono (fun x hx => propext (hq x hx))
  have heσ : f ⁻¹' Iic z =ᵐ[(σ : Measure ℝ)] Iic q :=
    hσ.mono (fun x hx => propext (hq x hx))
  change |(Measure.map f (ρ : Measure ℝ)).real (Iic z) - (Measure.map f (σ : Measure ℝ)).real (Iic z)| ≤ δ
  rw [map_measureReal_apply hf measurableSet_Iic, map_measureReal_apply hf measurableSet_Iic,
    measureReal_congr heρ, measureReal_congr heσ]
  exact h q

end RealCDFClose
end Blotto
