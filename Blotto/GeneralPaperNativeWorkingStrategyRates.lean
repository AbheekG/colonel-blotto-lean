import Blotto.GeneralPaperNativeWorkingDescriptionRates

/-! Sharp actual-domain original/source/strategy enclosing profiles. Work
price envelopes are used only inside encoded metadata fields. -/
namespace Blotto.GeneralPaperNativeWorkingStrategyRates
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperUniformResourceGrowth GeneralPaperNativeWorkingResourceRates GeneralPaperNativeWorkingDescriptionRates
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

theorem original_rate (model : RationalCostModel) :
    Bound (fun p => GeneralPaperOriginalSourceDriverConstructionStorage.originalProfile 1 (prepared model p).Qv (reduced model p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hOwner := owner_rate model
  unfold GeneralPaperOriginalSourceDriverConstructionStorage.originalProfile
  fun_prop

theorem return_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperOriginalSourceDriverConstructionStorage.returnProfile 1 (exponent p) (prepared model p).Qv
      (height model p) (reduced model p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hOriginal := original_rate model
  have hPhysical := physical_rate hg
  unfold GeneralPaperOriginalSourceDriverConstructionStorage.returnProfile
  fun_prop

theorem source_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperOriginalSourceDriverConstructionStorage.profile model C d 1 (exponent p) (originalSize p)
      (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hPrep := preparation_rate hg
  have hWhole := whole_rate hg
  have hOriginal := original_rate model
  have hReturn := return_rate hg
  have hPrice := source_price_small hg
  have hCap : Small (fun p => GeneralPaperOriginalSourceDriverConstructionStorage.cap model C d 1 (exponent p) (originalSize p)
      (prepared model p).Qv (ledger p) (reduced model p)) (logarithm model) := by
    unfold GeneralPaperOriginalSourceDriverConstructionStorage.cap
    fun_prop
  unfold GeneralPaperOriginalSourceDriverConstructionStorage.profile
  fun_prop (config := {maxSteps := 4000})

theorem prepared_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperOriginalStrategyConstructionStorage.preparedProfile 1 (exponent p) (prepared model p).Qv
      (height model p) (reduced model p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hOriginal := original_rate model
  have hDescription := description_return_rate hg
  unfold GeneralPaperOriginalStrategyConstructionStorage.preparedProfile
  fun_prop

theorem attach_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperOriginalStrategyConstructionStorage.attachProfile model 1 (exponent p) (prepared model p).Qv
      (height model p) (reduced model p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hReturn := return_rate hg
  have hDescription := description_rate hg
  have hPrepared := prepared_rate hg
  have hPrice := attach_price_small hg
  have hCap : Small (fun p => GeneralPaperOriginalStrategyConstructionStorage.attachCap model 1 (exponent p)
      (height model p) (reduced model p)) (logarithm model) := by
    unfold GeneralPaperOriginalStrategyConstructionStorage.attachCap
    fun_prop
  unfold GeneralPaperOriginalStrategyConstructionStorage.attachProfile
  fun_prop (config := {maxSteps := 4000})

theorem strategy_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperOriginalStrategyConstructionStorage.profile model C d 1 (exponent p) (originalSize p) (prepared model p).Qv
      (ledger p) (height model p) (reduced model p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hSource := source_rate hg
  have hAttach := attach_rate hg
  have hPrice := strategy_price_small hg
  have hCap : Small (fun p => GeneralPaperOriginalStrategyConstructionStorage.cap model C d 1 (exponent p) (originalSize p)
      (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (logarithm model) := by
    unfold GeneralPaperOriginalStrategyConstructionStorage.cap
    fun_prop
  unfold GeneralPaperOriginalStrategyConstructionStorage.profile
  fun_prop (config := {maxSteps := 4000})

end Blotto.GeneralPaperNativeWorkingStrategyRates
