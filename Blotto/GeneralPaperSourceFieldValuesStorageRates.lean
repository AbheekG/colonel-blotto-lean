import Blotto.GeneralPaperRetainedFieldValuesStorage

/-! The actual normalized-value constructor is linear in field count up
to proved logarithms. Copied values and primitive scratch come from the
short integer weights, not from a compiler-lifetime size bound. -/
namespace Blotto.GeneralPaperSourceFieldValuesStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

@[fun_prop]
theorem scaling (model : RationalCostModel) (m Q : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => GeneralPaperRetainedFieldValuesStorage.profile model W m Q) := by
  dsimp only [GeneralPaperRetainedFieldValuesStorage.profile,GeneralPaperRetainedFieldValuesStorage.width,GeneralPaperReducedValueArrayPrice.width,GeneralPaperRetainedFieldValuesStorage.callbackPrice,GeneralPaperRetainedFieldValuesStorage.scalarProfile,GeneralPaperRetainedFieldValuesStorage.scalarCap,GeneralPaperRetainedFieldValuesStorage.metadataCap,GeneralPaperRetainedFieldValuesStorage.price,GeneralPaperNativePayloadFillStorage.profile,GeneralPaperNativePayloadFillStorage.frameProfile,GeneralPaperNativePayloadFillStorage.metadataCap,GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperSummaryArrayExecution.arrayWord,GeneralPaperEncodedRationalRows.rowProfile,GeneralPaperEncodedScalarStorage.natBits]
  fun_prop

theorem model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m Q : ℕ) :
    GeneralPaperRetainedFieldValuesStorage.profile actual W m Q≤GeneralPaperRetainedFieldValuesStorage.profile upper W m Q := by
  dsimp only [GeneralPaperRetainedFieldValuesStorage.profile,GeneralPaperRetainedFieldValuesStorage.width,GeneralPaperReducedValueArrayPrice.width,GeneralPaperRetainedFieldValuesStorage.callbackPrice,GeneralPaperRetainedFieldValuesStorage.scalarProfile,GeneralPaperRetainedFieldValuesStorage.scalarCap,GeneralPaperRetainedFieldValuesStorage.metadataCap,GeneralPaperRetainedFieldValuesStorage.price,GeneralPaperNativePayloadFillStorage.profile,GeneralPaperNativePayloadFillStorage.frameProfile,GeneralPaperNativePayloadFillStorage.metadataCap,GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperSummaryArrayExecution.arrayWord,GeneralPaperEncodedRationalRows.rowProfile,GeneralPaperEncodedScalarStorage.natBits]
  gcongr <;> exact h _

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperRetainedFieldValuesStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperRetainedFieldValuesStorage.profile,GeneralPaperRetainedFieldValuesStorage.width,GeneralPaperReducedValueArrayPrice.width,GeneralPaperRetainedFieldValuesStorage.callbackPrice,GeneralPaperRetainedFieldValuesStorage.scalarProfile,GeneralPaperRetainedFieldValuesStorage.scalarCap,GeneralPaperRetainedFieldValuesStorage.metadataCap,GeneralPaperRetainedFieldValuesStorage.price,GeneralPaperNativePayloadFillStorage.profile,GeneralPaperNativePayloadFillStorage.frameProfile,GeneralPaperNativePayloadFillStorage.metadataCap,GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperSummaryArrayExecution.arrayWord,GeneralPaperEncodedRationalRows.rowProfile,GeneralPaperEncodedScalarStorage.natBits]
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(1,0,0) := rfl

@[fun_prop]
theorem price_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperRetainedFieldValuesStorage.price (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.Qv) := by
  have hw := of_tight hW
  dsimp only [GeneralPaperRetainedFieldValuesStorage.price,GeneralPaperRetainedFieldValuesStorage.width,GeneralPaperRetainedFieldValuesStorage.callbackPrice,GeneralPaperReducedValueArrayPrice.width,GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperSummaryArrayExecution.arrayWord]
  dsimp only [GeneralPaperFastRationalMajorant.model]
  fun_prop

end Blotto.GeneralPaperSourceFieldValuesStorageRates
