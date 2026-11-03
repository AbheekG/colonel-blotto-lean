import Blotto.PaperPRGControllerRecords

/-! The concrete cached sample's priced subroutines are covered by the
joined ledger. This links the actual normalization/array/initialization/
fallback/scaling execution to the arithmetic and overhead components, rather
than relying only on equal output data and a bound on an unrelated sum.
-/

namespace Blotto.PaperPRGConcretePriceCoverage
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem constructed_sample_work {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (PaperPRGInitializationFallbackCost.sample i model primitive W K bits).2 =
      rationalInitialDataBitCost model i.length i.initial+i.paperFallbackWork K bits+
        PaperPRGInitializationFallbackCost.systemExtra i primitive W K bits := by
  unfold PaperPRGInitializationFallbackCost.sample PaperPRGInitializationFallbackCost.systemExtra
    RationalLottoResourceSystem.paperFallbackWork
  rw [PaperPRGInitializationFallbackCost.fixedSample_work]
  dsimp only
  omega

def numeric {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  let system := PaperPRGNormalizedCache.source i rich
  rationalInitialDataBitCost model system.length system.initial+system.paperFallbackWork K bits+
    RationalScaleRowCode.rowBitCost model i.a (system.storedPaperSample K bits).allocation

theorem sample_work {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    (PaperPRGCachedDraw.sample p model primitive rich bits).2 =
      (PaperPRGNormalizedCache.build p.source model primitive (PRGPaperDrawCost.width p.source p.precision) rich).2+
        numeric p.source model rich p.precision bits+
        PaperPRGInitializationFallbackCost.originalExtra p.source primitive rich p.precision bits+
        PaperPRGConstructedDrawCost.scaleOverhead p.source primitive p.precision := by
  unfold PaperPRGCachedDraw.sample
  dsimp only
  rw [PaperStoredRowConstruction.scale_work,PaperPRGInitializationFallbackCost.sample_data,
    constructed_sample_work,PaperPRGNormalizedCache.build_system]
  unfold numeric PaperPRGInitializationFallbackCost.originalExtra PaperPRGNormalizedCache.source
    PaperPRGConstructedDrawCost.scaleOverhead
  cases rich <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring

theorem numeric_le_arithmetic {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    numeric i model rich K bits ≤ PRGPaperDrawCost.arithmeticWork i model primitive rich K bits := by
  unfold numeric PaperPRGNormalizedCache.source
  cases rich with
  | false =>
      simp only [Bool.false_eq_true,ite_false]
      rw [RationalLottoResourceSystem.storedPaperSample_allocation]
      change rationalInitialDataBitCost model i.normalizedInput.poorNativeSystem.length i.normalizedInput.poorNativeSystem.initial+
        i.normalizedInput.poorNativeSystem.paperFallbackWork K bits+i.poorScalingBitWork model K bits ≤ _
      simp only [PRGPaperDrawCost.arithmeticWork,Bool.false_eq_true,ite_false,
        RationalPRGOriginalInput.poorProcessingAndScalingWork,RationalPRGInput.poorSharedProcessingWork,
        RationalPRGInput.poorSharedSourceAndPackingWork,RationalPRGInput.poorSharedSourceProcessingAllowance,
        RationalPRGInput.poorSharedSourceDataAndReaderCost,RationalPRGInput.poorInitialDataBitCost]
      omega
  | true =>
      simp only [ite_true]
      rw [RationalLottoResourceSystem.storedPaperSample_allocation]
      change rationalInitialDataBitCost model i.normalizedInput.richNativeSystem.length i.normalizedInput.richNativeSystem.initial+
        i.normalizedInput.richNativeSystem.paperFallbackWork K bits+i.richScalingBitWork model K bits ≤ _
      simp only [PRGPaperDrawCost.arithmeticWork,ite_true,
        RationalPRGOriginalInput.richProcessingAndScalingWork,RationalPRGInput.richSharedProcessingWork,
        RationalPRGInput.richSharedSourceAndPackingWork,RationalPRGInput.richSharedSourceProcessingAllowance,
        RationalPRGInput.richSharedSourceDataAndReaderCost,RationalPRGInput.richInitialDataBitCost]
      omega

theorem concrete_sample_price_le_work {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    (PaperPRGCachedDraw.sample p model primitive rich bits).2 ≤
      PaperPRGControllerRecords.work p model primitive c rich bits := by
  have hPrice := sample_work p model primitive rich bits
  have hNumeric := numeric_le_arithmetic p.source model primitive rich p.precision bits
  unfold PaperPRGControllerRecords.work PaperPRGCachedDraw.work PaperPRGInitializationFallbackCost.work
    PaperPRGConstructedDrawCost.work PRGPaperDrawCost.work
  dsimp only
  omega

theorem concrete_sample_price_bound {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    (PaperPRGCachedDraw.sample p model primitive rich bits).2 ≤
      PaperPRGControllerRecords.bound p.source model c p.precision p.bytes.length :=
  (concrete_sample_price_le_work p model primitive c rich bits).trans
    (PaperPRGControllerRecords.work_bound p model primitive c hPrimitive rich bits)

end Blotto.PaperPRGConcretePriceCoverage
