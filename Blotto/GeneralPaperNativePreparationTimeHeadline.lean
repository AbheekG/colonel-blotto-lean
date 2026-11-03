import Blotto.GeneralPaperNativePreparationTimeRates

/-! Full actual unequal-budget bit-input preparation time and simultaneous
working-space/capacity at the same internally derived common word. Rates
retain additive original input/accuracy lengths in the paper epsilon units. -/
namespace Blotto.GeneralPaperNativePreparationTimeHeadline
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperNativeSourceTimeRates GeneralPaperNativePreparationTimeRates
open GeneralPaperNativeSourceTimeHeadline (timeScale structural_scale)
open GeneralPaperNativeWorkingSpaceHeadline (epsilon epsilon_positive exponent_exact paperLog log_comparison spaceScale)
open GeneralPaperOriginalSourceDriverConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem bit_price_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      (bitPrice model C d p:ℚ)≤(A:ℚ)*timeScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := bit_price_rate hg
  refine ⟨A*3241792*4^e,e,?_⟩
  intro p hOne
  have hRate := structural_scale model p hOne
  have hLog := log_comparison model p
  have hNat := (hA p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e))
  have hCast : (bitPrice model C d p:ℚ)≤
      (A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := by exact_mod_cast hNat
  calc
    _≤(A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := hCast
    _≤(A:ℚ)*(3241792*timeScale p)*((4:ℚ)*(paperLog p:ℚ))^e := by gcongr
    _= _ := by push_cast;rw [mul_pow];ring

theorem native_bit_time_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      let W := word model C d p
      ((GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).2:ℚ)≤
        (A:ℚ)*timeScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := bit_price_headline hg
  exact ⟨A,e,fun p hOne => (Nat.cast_le.mpr (native_bit_work hg p)).trans (hA p hOne)⟩

theorem simultaneous_time_space_capacity {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ At et As es : ℕ,∀ p : Problem,epsilon p<1 →
    let W := word model C d p
    let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1
    let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W k p.values p.selector p.correct).1
    ((GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).2:ℚ)≤
      (At:ℚ)*timeScale p*(paperLog p:ℚ)^et ∧
    ∀ (cS : SourceCursor actual.reduced.m k actual.Qv)
      (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor actual.reduced (GeneralPaperOriginalStrategyConstructionStorage.rows k actual.reduced)),
      let observed := GeneralPaperClosedStrategyConstructionStorage.window W
        (GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).1
        (GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).2
        (GeneralPaperAccuracyStrategyConstructionStorage.window model W p.words p.values p.selector p.correct p.budget p.budget_valid cS cD)
      (observed:ℚ)≤(As:ℚ)*spaceScale p*(paperLog p:ℚ)^es ∧ observed<2^W ∧
        GeneralPaperClosedDescriptionStorage.preparedFoot W
          (GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).1<2^W := by
  obtain ⟨At,et,hTime⟩ := native_bit_time_headline hg
  obtain ⟨As,es,hSpace⟩ := GeneralPaperNativeWorkingSpaceHeadline.native_bit_window_headline hg
  exact ⟨At,et,As,es,fun p hOne => ⟨hTime p hOne,hSpace p hOne⟩⟩

end Blotto.GeneralPaperNativePreparationTimeHeadline
