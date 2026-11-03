import Blotto.GeneralPaperClosedParsedStorage

/-! The sharp preparation-space rate at every enlarged logarithmic word,
and the actual parsed continuation at that word. -/
namespace Blotto.GeneralPaperEnlargedReferenceSpace
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperUniformResourceGrowth
open GeneralPaperEnlargedReferenceSourceTime (Reference)
open GeneralPaperNativeWorkingResourceRates (rate rate_positive)
open GeneralPaperNativeWorkingSpaceHeadline (epsilon paperLog spaceScale log_comparison structural_scale)
open GeneralPaperClosedParsedStorage (SourceCursor DescriptionCursor window)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem reserve_rate {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    Bound (fun p => reserve model C d (cal.word p) p) (rate model) (logarithm model) :=
  profile_at_word (reserve model C d) cal.word (rate model) (logarithm model)
    (fun p => GeneralPaperFullPreparationReference.scaling model C d (accuracySize p) (exponent p) (originalSize p)
      (prepared model p).Qv (ledger p) (height model p) (reduced model p) (source model p))
    cal.positive cal.tight (GeneralPaperNativeWorkingPreparationRates.reserve_at_one_rate hg)

theorem reserve_headline {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    ∃ A e : ℕ, ∀ p : Problem, epsilon p < 1 →
      (reserve model C d (cal.word p) p : ℚ) ≤ (A : ℚ) * spaceScale p * (paperLog p : ℚ) ^ e := by
  obtain ⟨A, e, hA⟩ := reserve_rate hg cal
  refine ⟨A * 810448 * 4 ^ e, e, fun p hOne => ?_⟩
  have hRate := structural_scale model p hOne
  have hLog := log_comparison model p
  have hNat := (hA p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e))
  have hCast : (reserve model C d (cal.word p) p : ℚ) ≤
      (A : ℚ) * (rate model p : ℚ) * ((4 : ℚ) * (paperLog p : ℚ)) ^ e := by exact_mod_cast hNat
  calc
    _ ≤ (A : ℚ) * (rate model p : ℚ) * ((4 : ℚ) * (paperLog p : ℚ)) ^ e := hCast
    _ ≤ (A : ℚ) * (810448 * spaceScale p) * ((4 : ℚ) * (paperLog p : ℚ)) ^ e := by gcongr
    _ = _ := by push_cast; rw [mul_pow]; ring

theorem parsed_window {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (p : Problem) :
    ∀ (cS : SourceCursor model (cal.word p) (GeneralPaperBinaryAccuracy.prepare (fun w => w) (cal.word p) p.words).1 p.values p.selector p.correct)
      (cD : DescriptionCursor model (cal.word p) (GeneralPaperBinaryAccuracy.prepare (fun w => w) (cal.word p) p.words).1 p.values p.selector p.correct),
      window model (cal.word p) (GeneralPaperBinaryAccuracy.prepare (fun w => w) (cal.word p) p.words).1 p.values p.selector p.correct p.budget p.budget_valid cS cD ≤
        reserve model C d (cal.word p) p := by
  have h := GeneralPaperNativeReferenceEnlargement.bit_contract hg p (cal.word p) (cal.above p)
  have hSkip := GeneralPaperClosedParsedStorage.le_redundant_accuracy model (cal.word p) p.words
    p.values p.selector p.correct p.budget p.budget_valid
  dsimp only at h hSkip
  exact fun cS cD => (hSkip cS cD).trans (h cS cD).1

theorem returned_covered {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (p : Problem) :
    ∀ (_cS : SourceCursor model (cal.word p) (GeneralPaperBinaryAccuracy.prepare (fun w => w) (cal.word p) p.words).1 p.values p.selector p.correct)
      (_cD : DescriptionCursor model (cal.word p) (GeneralPaperBinaryAccuracy.prepare (fun w => w) (cal.word p) p.words).1 p.values p.selector p.correct),
      GeneralPaperClosedDescriptionStorage.preparedFoot (cal.word p)
        (GeneralPaperClosedStrategyDriver.bit model (cal.word p) (cal.word p) (cal.word p)
          p.words p.values p.selector p.correct p.budget p.budget_valid).1 ≤
        reserve model C d (cal.word p) p := by
  have h := GeneralPaperNativeReferenceEnlargement.bit_contract hg p (cal.word p) (cal.above p)
  have hReturn := GeneralPaperClosedStrategyConstructionStorage.returned_covered (cal.word p)
    (GeneralPaperAccuracyStrategyDriver.bit model (cal.word p) (cal.word p) (cal.word p)
      p.words p.values p.selector p.correct p.budget p.budget_valid).1
    (GeneralPaperAccuracyStrategyDriver.bit model (cal.word p) (cal.word p) (cal.word p)
      p.words p.values p.selector p.correct p.budget p.budget_valid).2
  dsimp only at h
  intro cS cD
  exact (hReturn _).trans (h cS cD).1

end Blotto.GeneralPaperEnlargedReferenceSpace
