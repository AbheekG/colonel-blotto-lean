import Blotto.PlayerSpecificFairBitBlocks

/-! Averaging fresh finite packets preserves a uniform bounded-test error.
The order of two fair packets is used only in these law proofs. -/
namespace Blotto.PlayerSpecificFairAveraging
open MeasureTheory
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem swap (R S : ℕ) (f : (Fin R → Bool) → (Fin S → Bool) → ℝ) :
    (∫ bits,f (firstBitBlock R S bits) (secondBitBlock R S bits)
      ∂(fairBitLaw (R+S) : Measure (Fin (R+S) → Bool)))=
      ∫ second,(∫ first,f first second ∂(fairBitLaw R : Measure (Fin R → Bool)))
        ∂(fairBitLaw S : Measure (Fin S → Bool)) := by
  rw [PlayerSpecificFairBitBlocks.integral_blocks]
  exact integral_integral_swap Integrable.of_finite

theorem error (K : ℕ) (a b : (Fin K → Bool) → ℝ) (E : ℝ)
    (h : ∀ bits,|a bits-b bits| ≤ E) :
    |(∫ bits,a bits ∂(fairBitLaw K : Measure (Fin K → Bool)))-
      (∫ bits,b bits ∂(fairBitLaw K : Measure (Fin K → Bool)))| ≤ E := by
  have hlo : ∀ bits,b bits-E ≤ a bits := fun bits => by
    have hb := (abs_le.mp (h bits)).1
    linarith only [hb]
  have hhi : ∀ bits,a bits ≤ b bits+E := fun bits => by
    have hb := (abs_le.mp (h bits)).2
    linarith only [hb]
  have lo := integral_mono (μ := (fairBitLaw K : Measure (Fin K → Bool)))
    Integrable.of_finite Integrable.of_finite hlo
  have hi := integral_mono (μ := (fairBitLaw K : Measure (Fin K → Bool)))
    Integrable.of_finite Integrable.of_finite hhi
  rw [integral_sub Integrable.of_finite Integrable.of_finite,integral_const,probReal_univ,one_smul] at lo
  rw [integral_add Integrable.of_finite Integrable.of_finite,integral_const,probReal_univ,one_smul] at hi
  exact abs_le.mpr ⟨by linarith only [lo],by linarith only [hi]⟩

theorem event (K : ℕ) {α : Type*} [MeasurableSpace α] (sample : (Fin K → Bool) → α)
    (A : Set α) (hA : MeasurableSet A) :
    ((fairBitLaw K).map sample : Measure α).real A=
      ∫ bits,(if sample bits ∈ A then (1:ℝ) else 0) ∂(fairBitLaw K : Measure (Fin K → Bool)) := by
  classical
  change (Measure.map sample (fairBitLaw K : Measure (Fin K → Bool))).real A= _
  rw [map_measureReal_apply (measurable_of_countable _) hA]
  have he : (fun bits => if sample bits ∈ A then (1:ℝ) else 0)=
      (sample ⁻¹' A).indicator (fun _ => (1:ℝ)) := by
    funext bits
    simp only [Set.indicator_apply,Set.mem_preimage]
  rw [he,integral_indicator_const _ ((measurable_of_countable sample) hA),smul_eq_mul,mul_one]

end Blotto.PlayerSpecificFairAveraging
