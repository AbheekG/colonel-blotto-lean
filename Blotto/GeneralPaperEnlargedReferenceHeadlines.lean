import Blotto.GeneralPaperEnlargedReferenceDescription

/-! Sharp bit-time headlines at an arbitrary enlarged logarithmic word,
with one measured coefficient still covering the complete equal envelope. -/
namespace Blotto.GeneralPaperEnlargedReferenceHeadlines
open GeneralPaperNativeResourceDomain
open GeneralPaperEnlargedReferenceSourceTime (Reference)
open GeneralPaperEnlargedReferencePreparationTime
open GeneralPaperNativeSourceTimeRates (rate)
open GeneralPaperNativeSourceTimeHeadline (timeScale structural_scale)
open GeneralPaperNativeWorkingSpaceHeadline (epsilon paperLog log_comparison)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem bit_price_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      (bitPrice model C d cal p:ℚ)≤(A:ℚ)*timeScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := bit_price_rate hg cal
  refine ⟨A*3241792*4^e,e,?_⟩
  intro p hOne
  have hRate := structural_scale model p hOne
  have hLog := log_comparison model p
  have hNat := (hA p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e))
  have hCast : (bitPrice model C d cal p:ℚ)≤
      (A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := by exact_mod_cast hNat
  calc
    _≤(A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := hCast
    _≤(A:ℚ)*(3241792*timeScale p)*((4:ℚ)*(paperLog p:ℚ))^e := by gcongr
    _= _ := by push_cast;rw [mul_pow];ring

theorem native_bit_time_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      let W := cal.word p
      ((GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).2:ℚ)≤
        (A:ℚ)*timeScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := bit_price_headline hg cal
  exact ⟨A,e,fun p hOne => (Nat.cast_le.mpr (native_bit_work hg cal p)).trans (hA p hOne)⟩


theorem measured_calibration {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧
      ∀ p : GeneralPaperOriginalGameInput.Input,
        GeneralPaperStoredPreparationUniformCapacity.envelope model K
          (GeneralPaperOriginalGameInput.equalInput model p) <
            2 ^ (K * GeneralPaperOriginalReferenceComparison.logarithm model p) := by
  obtain ⟨K, hK, hSafe⟩ := GeneralPaperAllBranchReferenceCalibration.uniform_calibration hg
  let cal : Reference model C d :=
    ⟨GeneralPaperMeasuredReferenceGrowth.word model K, GeneralPaperMeasuredReferenceGrowth.positive model K hK,
      GeneralPaperMeasuredReferenceGrowth.word_tight model K, fun p =>
        (hSafe (GeneralPaperMeasuredReferenceGrowth.original p)).2 p.budget_valid.2⟩
  exact ⟨K, hK, cal, rfl, fun p => (hSafe p).1⟩

end Blotto.GeneralPaperEnlargedReferenceHeadlines
