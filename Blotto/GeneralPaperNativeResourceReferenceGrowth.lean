import Blotto.GeneralPaperReducedInputPreparationGrowth

/-! The full reserve is analyzed at word one on actual original problems.
Old unconditional source envelopes pull back along retained first/reduced
source records. Uniform positive scaling then calibrates one native word. -/
namespace Blotto.GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperUniformResourceGrowth
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

def rows (model : RationalCostModel) (p : Problem) : ℕ := GeneralPaperOriginalStrategyConstructionStorage.rows (exponent p) (reduced model p)
def labels (model : RationalCostModel) (p : Problem) : ℕ := (GeneralPaperProxyParameters.prepare (reduced model p).m (exponent p)).K
def height (model : RationalCostModel) (p : Problem) : ℕ := GeneralPaperSourcePairAnchorHeights.width (reduced model p).m (exponent p)

@[fun_prop]
theorem rows_small (model : RationalCostModel) : Small (rows model) (logarithm model) :=
  pullback_source_small GeneralPaperNativeSourceWordGrowth.rows_small (source model)

@[fun_prop]
theorem labels_small (model : RationalCostModel) : Small (labels model) (logarithm model) :=
  pullback_source_small GeneralPaperCompilerReferenceGrowth.labels_small (source model)

@[fun_prop]
theorem height_small (model : RationalCostModel) : Small (height model) (logarithm model) :=
  pullback_source_small GeneralPaperSortedConstructionProfileRates.anchor_small (source model)

theorem preparation_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperOriginalSourcePreparationStorage.preparationProfile model 1 (exponent p) (originalSize p)
      (reduced model p).denominator (GeneralPaperValueRoundingInputPrice.inputSize (reduced model p).values) (reduced model p)) (logarithm model) := by
  have hEnvelope := pullback_small_with_log (GeneralPaperReducedInputPreparationGrowth.preparation_small hg)
    (originalSource model) (logarithm model) (original_source_log_tight model)
  apply small_mono hEnvelope
  intro p
  change _≤GeneralPaperOriginalSourcePreparationStorage.preparationProfile model 1 (exponent p) (ledger p)
    (reduced model p).denominator
    (GeneralPaperValueRoundingInputPrice.inputSize (GeneralPaperReducedInputPreparationGrowth.output model (originalSource model p)).values)
    (GeneralPaperReducedInputPreparationGrowth.output model (originalSource model p))
  unfold GeneralPaperReducedInputPreparationGrowth.output
  rw [←original_source_reduction model p]
  exact GeneralPaperReducedInputPreparationGrowth.preparation_profile_mono model 1 (exponent p) (originalSize p) (ledger p)
    (reduced model p).denominator _ (reduced model p) (by unfold ledger originalInputSize;omega)

theorem preparation_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperOriginalSourcePreparationStorage.preparationPrice model 1 (exponent p) (originalSize p)
      (reduced model p).denominator (GeneralPaperValueRoundingInputPrice.inputSize (reduced model p).values) (reduced model p)) (logarithm model) := by
  have hEnvelope := pullback_small_with_log (GeneralPaperReducedInputPreparationGrowth.preparation_price_small hg)
    (originalSource model) (logarithm model) (original_source_log_tight model)
  apply small_mono hEnvelope
  intro p
  change _≤GeneralPaperOriginalSourcePreparationStorage.preparationPrice model 1 (exponent p) (ledger p)
    (reduced model p).denominator
    (GeneralPaperValueRoundingInputPrice.inputSize (GeneralPaperReducedInputPreparationGrowth.output model (originalSource model p)).values)
    (GeneralPaperReducedInputPreparationGrowth.output model (originalSource model p))
  unfold GeneralPaperReducedInputPreparationGrowth.output
  rw [←original_source_reduction model p]
  exact GeneralPaperReducedInputPreparationGrowth.preparation_price_mono model 1 (exponent p) (originalSize p) (ledger p)
    (reduced model p).denominator _ (reduced model p) (by unfold ledger originalInputSize;omega)

theorem whole_profile_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperFastWholeDriverStorage.profile model C d 1 (reduced model p).m (exponent p)
      (prepared model p).Qv (ledger p)) (logarithm model) := by
  have hr : GeneralPaperSourceWordGrowth.Small GeneralPaperFastFrontStorageRates.rate := by
    have hp := GeneralPaperSourceWordGrowth.pow_two _ GeneralPaperSourceWordGrowth.k_tight
    unfold GeneralPaperFastFrontStorageRates.rate GeneralPaperSourceRateAlgebra.monomial
      GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
    fun_prop
  exact bound_small (logarithm_positive model) (whole_space_at_one hg) (pullback_source_small hr (source model))

def rowEnvelope (model : RationalCostModel) (p : Problem) : ℕ :=
  GeneralPaperCachedRowConstructionStorage.profile model 1 (rows model p) (reduced model p).m (reduced model p).m
    (labels model p) (1+2*height model p)

theorem row_envelope_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (rowEnvelope model) (logarithm model) := by
  have h := GeneralPaperSortedConstructionProfileRates.native_profile hg (fun _ => 1)
    (GeneralPaperSourceWordGrowth.tight_constant 1) GeneralPaperSourceWordGrowth.Input.m GeneralPaperSourceWordGrowth.Input.m
    (fun _ => le_rfl) (fun _ => le_rfl)
  have hr : GeneralPaperSourceWordGrowth.Small (GeneralPaperSourceRateAlgebra.monomial 2 0 3) := by
    have hp := GeneralPaperSourceWordGrowth.pow_two _ GeneralPaperSourceWordGrowth.k_tight
    unfold GeneralPaperSourceRateAlgebra.monomial GeneralPaperNativeSourceRates.fields
      GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
    fun_prop
  exact pullback_source_small (GeneralPaperSourceRowsStorageRates.soft_small h hr) (source model)

theorem physical_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperStrategyDescriptionConstructionStorage.physicalProfile 1 (rows model p)
      (reduced model p).m (labels model p) (height model p)) (logarithm model) := by
  have hL := logarithm_positive model
  unfold GeneralPaperStrategyDescriptionConstructionStorage.physicalProfile GeneralPaperEnclosingSourceOwners.columnsProfile
    GeneralPaperEnclosingSourceOwners.columnProfile
  fun_prop (config := {maxSteps := 4000})

theorem description_return_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperClosedDescriptionStorage.descriptionProfile 1 (rows model p) (labels model p)
      (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  unfold GeneralPaperClosedDescriptionStorage.descriptionProfile GeneralPaperCachedCircleRetainedStorage.commonProfile
    GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile GeneralPaperEnclosingSourceOwners.columnsProfile
    GeneralPaperEnclosingSourceOwners.columnProfile
  fun_prop (config := {maxSteps := 4000})

theorem description_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperStrategyDescriptionConstructionStorage.price model 1 (rows model p)
      (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  unfold GeneralPaperStrategyDescriptionConstructionStorage.price GeneralPaperCachedPairConstructionStorage.price
    GeneralPaperSharedCacheConstructionStorage.originalPrice GeneralPaperSharedCacheConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.price GeneralPaperCircleCoefficientConstructionStorage.callbackPrice
    GeneralPaperCircleArcConstructionStorage.price GeneralPaperSharedCacheConstructionStorage.magnitude
    GeneralPaperCircleRationalCoefficients.width GeneralPaperCachedRowConstructionStorage.price
    GeneralPaperCachedRowConstructionStorage.rowPrice GeneralPaperSortedReferenceConstructionStorage.price
    GeneralPaperRepresentativeSortStorage.price GeneralPaperNativeRepresentativeSort.profile
    GeneralPaperPricedSort.profile GeneralPaperNativePayloadFillStorage.workCap
  fun_prop (config := {maxSteps := 4000})

theorem common_extra_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperCacheConstructionGrowth.extraProfile model 1 p.n (reduced model p).classified.light.size
      (reduced model p).representatives (reduced model p).classified.lightWeight) (logarithm model) := by
  have hL := logarithm_positive model
  unfold GeneralPaperCacheConstructionGrowth.extraProfile GeneralPaperSharedCacheConstructionStorage.lightScalarProfile
    GeneralPaperSharedCacheConstructionStorage.profile GeneralPaperCircleCoefficientConstructionStorage.profile
    GeneralPaperCircleCoefficientConstructionStorage.scalarProfile GeneralPaperCircleCoefficientConstructionStorage.scalarCap
    GeneralPaperCircleCoefficientConstructionStorage.metadataCap GeneralPaperCircleCoefficientConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.callbackPrice GeneralPaperCircleRationalCoefficients.width
    GeneralPaperCircleArcConstructionStorage.profile GeneralPaperCircleArcConstructionStorage.frameProfile
    GeneralPaperCircleArcConstructionStorage.cap GeneralPaperCircleArcConstructionStorage.price
    GeneralPaperSharedCacheConstructionStorage.cap GeneralPaperSharedCacheConstructionStorage.price
    GeneralPaperSharedCacheConstructionStorage.magnitude GeneralPaperNativePayloadFillStorage.workCap
    GeneralPaperStockListPayloadStorage.ofFnProfile GeneralPaperCachedCircleRetainedStorage.commonProfile
  dsimp only [GeneralPaperCircleCoefficientConstructionStorage.price,GeneralPaperCircleCoefficientConstructionStorage.callbackPrice,
    GeneralPaperCircleRationalCoefficients.width,GeneralPaperCircleArcConstructionStorage.price,
    GeneralPaperSharedCacheConstructionStorage.magnitude,GeneralPaperNativePayloadFillStorage.workCap]
  fun_prop (config := {maxSteps := 4000})

theorem cache_cap_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperCachedPairConstructionStorage.cap model 1 (rows model p) (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hPrice : Small (fun p => GeneralPaperCachedPairConstructionStorage.price model 1 (rows model p) (height model p) (reduced model p)) (logarithm model) := by
    apply small_mono (description_price_small hg)
    intro p
    unfold GeneralPaperStrategyDescriptionConstructionStorage.price
    omega
  unfold GeneralPaperCachedPairConstructionStorage.cap
  fun_prop

theorem selected_child_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperStrategyDescriptionConstructionStorage.childProfile model 1 (rows model p) (labels model p)
      (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hOwner := owner_small model (fun _ => 1) (small_constant 1 _ hL)
  have hCommon := common_extra_small hg
  have hRows := row_envelope_small hg
  have hCap := cache_cap_small hg
  apply small_mono (g:=fun p => GeneralPaperOriginalReductionRetainedStorage.footprint 1 (reduced model p)+
    2*GeneralPaperCacheConstructionGrowth.extraProfile model 1 p.n (reduced model p).classified.light.size
      (reduced model p).representatives (reduced model p).classified.lightWeight+
    4*rowEnvelope model p+9*(natBits (GeneralPaperCachedPairConstructionStorage.cap model 1 (rows model p) (height model p) (reduced model p))+1)+192)
    (by fun_prop (config := {maxSteps := 4000}))
  intro p
  unfold GeneralPaperStrategyDescriptionConstructionStorage.childProfile
  split_ifs with he
  · have hm := (GeneralPaperNativeReductionShape.original_shape false model 1 (exponent p) p.values he).1
    change (reduced model p).m=(reduced model p).classified.heavy.size+(reduced model p).representatives at hm
    have hRowsBound := GeneralPaperSortedConstructionProfileRates.parameters_mono model 1 (rows model p) (rows model p)
      (reduced model p).classified.heavy.size (reduced model p).m (reduced model p).representatives (reduced model p).m
      (labels model p) (labels model p) (1+2*height model p) (1+2*height model p)
      le_rfl (by omega) (by omega) le_rfl le_rfl
    have hBound := GeneralPaperCacheConstructionGrowth.pair_profile_bound model 1 (rows model p) (labels model p) (height model p) (reduced model p)
    change _≤GeneralPaperOriginalReductionRetainedStorage.footprint 1 (reduced model p)+
      2*GeneralPaperCacheConstructionGrowth.extraProfile model 1 p.n (reduced model p).classified.light.size
        (reduced model p).representatives (reduced model p).classified.lightWeight+
      4*rowEnvelope model p+9*(natBits (GeneralPaperCachedPairConstructionStorage.cap model 1 (rows model p) (height model p) (reduced model p))+1)+192
    unfold rowEnvelope
    omega
  · exact Nat.zero_le _

theorem description_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperStrategyDescriptionConstructionStorage.profile model 1 (rows model p) (labels model p)
      (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hOwner := owner_small model (fun _ => 1) (small_constant 1 _ hL)
  have hPhysical := physical_small model
  have hReturn := description_return_small model
  have hChild := selected_child_small hg
  have hPrice := description_price_small hg
  have hCap : Small (fun p => GeneralPaperStrategyDescriptionConstructionStorage.cap model 1 (rows model p) (labels model p)
      (height model p) (reduced model p)) (logarithm model) := by
    unfold GeneralPaperStrategyDescriptionConstructionStorage.cap
    fun_prop
  unfold GeneralPaperStrategyDescriptionConstructionStorage.profile
  fun_prop (config := {maxSteps := 4000})

theorem original_profile_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperOriginalSourceDriverConstructionStorage.originalProfile 1 (prepared model p).Qv (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hOwner := owner_small model (fun _ => 1) (small_constant 1 _ hL)
  unfold GeneralPaperOriginalSourceDriverConstructionStorage.originalProfile
  fun_prop

theorem return_profile_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperOriginalSourceDriverConstructionStorage.returnProfile 1 (exponent p) (prepared model p).Qv
      (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hOriginal := original_profile_small model
  have hPhysical := physical_small model
  unfold GeneralPaperOriginalSourceDriverConstructionStorage.returnProfile
  fun_prop

theorem source_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperOriginalSourceDriverConstructionStorage.price model C d 1 (exponent p) (originalSize p)
      (prepared model p).Qv (ledger p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hPrep := preparation_price_small hg
  have hWhole := whole_price_at_one_small hg
  unfold GeneralPaperOriginalSourceDriverConstructionStorage.price
  fun_prop

theorem source_profile_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperOriginalSourceDriverConstructionStorage.profile model C d 1 (exponent p) (originalSize p)
      (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hPrep := preparation_small hg
  have hWhole := whole_profile_small hg
  have hOriginal := original_profile_small model
  have hReturn := return_profile_small model
  have hPrice := source_price_small hg
  have hCap : Small (fun p => GeneralPaperOriginalSourceDriverConstructionStorage.cap model C d 1 (exponent p) (originalSize p)
      (prepared model p).Qv (ledger p) (reduced model p)) (logarithm model) := by
    unfold GeneralPaperOriginalSourceDriverConstructionStorage.cap
    fun_prop
  unfold GeneralPaperOriginalSourceDriverConstructionStorage.profile
  fun_prop (config := {maxSteps := 4000})

theorem prepared_profile_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperOriginalStrategyConstructionStorage.preparedProfile 1 (exponent p) (prepared model p).Qv
      (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hOriginal := original_profile_small model
  have hDescription := description_return_small model
  unfold GeneralPaperOriginalStrategyConstructionStorage.preparedProfile
  fun_prop

theorem attach_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperOriginalStrategyConstructionStorage.attachPrice model 1 (exponent p)
      (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hDescription := description_price_small hg
  unfold GeneralPaperOriginalStrategyConstructionStorage.attachPrice
  fun_prop

theorem attach_profile_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperOriginalStrategyConstructionStorage.attachProfile model 1 (exponent p) (prepared model p).Qv
      (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hReturn := return_profile_small model
  have hDescription := description_small hg
  have hPrepared := prepared_profile_small model
  have hPrice := attach_price_small hg
  have hCap : Small (fun p => GeneralPaperOriginalStrategyConstructionStorage.attachCap model 1 (exponent p)
      (height model p) (reduced model p)) (logarithm model) := by
    unfold GeneralPaperOriginalStrategyConstructionStorage.attachCap
    fun_prop
  unfold GeneralPaperOriginalStrategyConstructionStorage.attachProfile
  fun_prop (config := {maxSteps := 4000})

theorem strategy_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperOriginalStrategyConstructionStorage.price model C d 1 (exponent p) (originalSize p) (prepared model p).Qv
      (ledger p) (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hSource := source_price_small hg
  have hAttach := attach_price_small hg
  unfold GeneralPaperOriginalStrategyConstructionStorage.price
  fun_prop

theorem strategy_profile_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperOriginalStrategyConstructionStorage.profile model C d 1 (exponent p) (originalSize p) (prepared model p).Qv
      (ledger p) (height model p) (reduced model p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hSource := source_profile_small hg
  have hAttach := attach_profile_small hg
  have hPrice := strategy_price_small hg
  have hCap : Small (fun p => GeneralPaperOriginalStrategyConstructionStorage.cap model C d 1 (exponent p) (originalSize p)
      (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (logarithm model) := by
    unfold GeneralPaperOriginalStrategyConstructionStorage.cap
    fun_prop
  unfold GeneralPaperOriginalStrategyConstructionStorage.profile
  fun_prop (config := {maxSteps := 4000})

theorem accuracy_price_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperBinaryAccuracyConstructionStorage.price 1 (accuracySize p)) (logarithm model) := by
  have hL := logarithm_positive model
  unfold GeneralPaperBinaryAccuracyConstructionStorage.price GeneralPaperAccuracyCountConstructionStorage.price
    GeneralPaperAccuracyCountConstructionStorage.step GeneralPaperAccuracyCountConstructionStorage.width
  fun_prop

theorem reader_price_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperFramedAccuracyConstructionStorage.price 1 (accuracySize p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hAccuracy := accuracy_price_small model
  unfold GeneralPaperFramedAccuracyConstructionStorage.price
  fun_prop

theorem accuracy_profile_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperBinaryAccuracyConstructionStorage.profile 1 (accuracySize p)) (logarithm model) := by
  have hRate := GeneralPaperBinaryAccuracyConstructionStorage.profile_rate (fun _ => 1) GeneralPaperSourceWordGrowth.Input.B
    (GeneralPaperSourceWordGrowth.tight_constant 1) GeneralPaperSourceWordGrowth.B_small
  have hSmall := GeneralPaperSourceRowsStorageRates.soft_small hRate (by fun_prop)
  apply small_mono (pullback_source_small hSmall (source model))
  intro p
  exact GeneralPaperFramedAccuracyConstructionStorage.word_profile_mono 1 (accuracySize p) (ledger p) (by unfold ledger;omega)

theorem positive_read_profile_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperPositiveWordReadConstructionStorage.profile 1 (accuracySize p)) (logarithm model) := by
  have hL := logarithm_positive model
  unfold GeneralPaperPositiveWordReadConstructionStorage.profile GeneralPaperPositiveWordReadConstructionStorage.inputProfile
    GeneralPaperPositiveWordReadConstructionStorage.returnProfile GeneralPaperAccuracyReadMetadataStorage.stepsProfile
    GeneralPaperAccuracyReadMetadataStorage.lengthProfile GeneralPaperBooleanRulerWorkStorage.budget
  fun_prop (config := {maxSteps := 4000})

theorem reader_profile_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperFramedAccuracyConstructionStorage.profile 1 (accuracySize p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hPositive := positive_read_profile_small model
  have hAccuracy := accuracy_profile_small model
  have hPrice := reader_price_small model
  unfold GeneralPaperFramedAccuracyConstructionStorage.profile GeneralPaperFramedAccuracyConstructionStorage.returnProfile
    GeneralPaperFramedAccuracyConstructionStorage.cap
  fun_prop

theorem close_price_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperClosedStrategyConstructionStorage.closePrice 1 (rows model p) (exponent p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hPrice := GeneralPaperSamplerControlsConstructionStorage.price_poly GeneralPaperClosedSamplerConstructionStorage.index_growth
    (fun _ => 1) (fun x => (GeneralPaperTrajectoryParameters.prepare (GeneralPaperSourceWordGrowth.alphabet x).lambda x.k).rows)
    (GeneralPaperSourceWordGrowth.tight_constant 1) GeneralPaperNativeSourceWordGrowth.rows_small
  have hNative := pullback_source_small (GeneralPaperCacheConstructionGrowth.small_of_poly hPrice) (source model)
  unfold GeneralPaperClosedStrategyConstructionStorage.closePrice
  fun_prop

theorem close_extra_small (model : RationalCostModel) :
    Small (fun p => GeneralPaperClosedSamplerConstructionStorage.extraProfile 1 p.n (rows model p) (labels model p)
      (exponent p) (reduced model p).m) (logarithm model) := by
  have hExtra := GeneralPaperClosedSamplerConstructionStorage.extra_poly (fun _ => 1) GeneralPaperSourceWordGrowth.Input.B
    (fun x => (GeneralPaperTrajectoryParameters.prepare (GeneralPaperSourceWordGrowth.alphabet x).lambda x.k).rows)
    (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).K) GeneralPaperSourceWordGrowth.Input.m
    (GeneralPaperSourceWordGrowth.tight_constant 1) GeneralPaperSourceWordGrowth.B_small
    GeneralPaperNativeSourceWordGrowth.rows_small GeneralPaperCompilerReferenceGrowth.labels_small GeneralPaperSourceWordGrowth.m_small
  have hNative := pullback_source_small (GeneralPaperCacheConstructionGrowth.small_of_poly hExtra) (source model)
  apply small_mono hNative
  intro p
  have hn := GeneralPaperOriginalValueBitDriverRate.input_fields p.values
  change p.n≤originalSize p at hn
  have hLedger : p.n≤ledger p := by unfold ledger originalInputSize;omega
  change GeneralPaperClosedSamplerConstructionStorage.extraProfile 1 p.n (rows model p) (labels model p) (exponent p) (reduced model p).m≤
    GeneralPaperClosedSamplerConstructionStorage.extraProfile 1 (ledger p) (rows model p) (labels model p) (exponent p) (reduced model p).m
  unfold GeneralPaperClosedSamplerConstructionStorage.extraProfile GeneralPaperClosedSamplerConstructionStorage.cap
    GeneralPaperSamplerControlsConstructionStorage.extraProfile GeneralPaperSamplerControlsConstructionStorage.cap natBits
  gcongr

theorem raw_prices_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperAccuracyStrategyConstructionStorage.price model C d 1 (accuracySize p) (exponent p)
      (originalSize p) (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (logarithm model) ∧
    Small (fun p => GeneralPaperFramedStrategyConstructionStorage.price model C d 1 (accuracySize p) (exponent p)
      (originalSize p) (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (logarithm model) ∧
    Small (fun p => GeneralPaperFramedStrategyConstructionStorage.rejectedPrice 1 (accuracySize p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hRoot := strategy_price_small hg
  have hAccuracy := accuracy_price_small model
  have hReader := reader_price_small model
  refine ⟨?_,?_,?_⟩
  · unfold GeneralPaperAccuracyStrategyConstructionStorage.price GeneralPaperAccuracyStrategyConstructionStorage.exponentPrice
    fun_prop
  · unfold GeneralPaperFramedStrategyConstructionStorage.price GeneralPaperAccuracyStrategyConstructionStorage.exponentPrice
    fun_prop
  · unfold GeneralPaperFramedStrategyConstructionStorage.rejectedPrice
    fun_prop

theorem raw_profiles_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (fun p => GeneralPaperAccuracyStrategyConstructionStorage.profile model C d 1 (accuracySize p) (exponent p)
      (originalSize p) (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (logarithm model) ∧
    Small (fun p => GeneralPaperFramedStrategyConstructionStorage.profile model C d 1 (accuracySize p) (exponent p)
      (originalSize p) (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (logarithm model) ∧
    Small (fun p => GeneralPaperFramedStrategyConstructionStorage.rejectedProfile 1 (accuracySize p) p.n (originalSize p) (ledger p)) (logarithm model) := by
  have hL := logarithm_positive model
  have hRoot := strategy_profile_small hg
  have hRootPrice := strategy_price_small hg
  have hAccuracy := accuracy_profile_small model
  have hReader := reader_profile_small model
  obtain ⟨hBitPrice,hFramePrice,hRejectPrice⟩ := raw_prices_small hg
  have hExp : Small (fun p => GeneralPaperAccuracyStrategyConstructionStorage.exponentProfile model C d 1 (exponent p)
      (originalSize p) (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (logarithm model) := by
    unfold GeneralPaperAccuracyStrategyConstructionStorage.exponentProfile GeneralPaperAccuracyStrategyConstructionStorage.ownerTail
      GeneralPaperAccuracyStrategyConstructionStorage.exponentCap GeneralPaperAccuracyStrategyConstructionStorage.exponentPrice
    fun_prop (config := {maxSteps := 4000})
  refine ⟨?_,?_,?_⟩
  · unfold GeneralPaperAccuracyStrategyConstructionStorage.profile GeneralPaperAccuracyStrategyConstructionStorage.cap
    fun_prop (config := {maxSteps := 4000})
  · unfold GeneralPaperFramedStrategyConstructionStorage.profile GeneralPaperFramedStrategyConstructionStorage.cap
    fun_prop (config := {maxSteps := 4000})
  · unfold GeneralPaperFramedStrategyConstructionStorage.rejectedProfile GeneralPaperFramedStrategyConstructionStorage.rejectedCap
    fun_prop (config := {maxSteps := 4000})

noncomputable def reserve (model : RationalCostModel) (C d W : ℕ) (p : Problem) : ℕ :=
  GeneralPaperFullPreparationReference.reserve model C d W (accuracySize p) (exponent p) (originalSize p)
    (prepared model p).Qv (ledger p) (height model p) (reduced model p) (source model p)

theorem reserve_at_one_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Small (reserve model C d 1) (logarithm model) := by
  have hL := logarithm_positive model
  obtain ⟨hBitPrice,hFramePrice,hRejectPrice⟩ := raw_prices_small hg
  obtain ⟨hBit,hFrame,hReject⟩ := raw_profiles_small hg
  have hClose := close_price_small model
  have hExtra := close_extra_small model
  have hSource := pullback_source_small (GeneralPaperFastDriverReference.at_one_small C d) (source model)
  unfold reserve GeneralPaperFullPreparationReference.reserve GeneralPaperFullPreparationReference.bitProfile
    GeneralPaperFullPreparationReference.frameProfile GeneralPaperFullPreparationReference.rejectedProfile
    GeneralPaperFullPreparationReference.indexSize GeneralPaperClosedStrategyConstructionStorage.frameProfile
    GeneralPaperClosedStrategyConstructionStorage.profile GeneralPaperClosedStrategyConstructionStorage.rejectedProfile
    GeneralPaperClosedStrategyConstructionStorage.cap GeneralPaperClosedStrategyConstructionStorage.price
    GeneralPaperClosedStrategyConstructionStorage.rejectedCap GeneralPaperClosedStrategyConstructionStorage.rejectedPrice
  fun_prop (config := {maxSteps := 4000})

noncomputable def word (model : RationalCostModel) (C d : ℕ) (p : Problem) : ℕ :=
  GeneralPaperFullPreparationReference.width model C d (accuracySize p) (exponent p) (originalSize p)
    (prepared model p).Qv (ledger p) (height model p) (reduced model p) (source model p)

theorem word_tight {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Tight (word model C d) (logarithm model) := by
  have hL := logarithm_positive model
  have hReserve := reserve_at_one_small hg
  have hPrior := prior_source_word_tight model C d
  unfold word GeneralPaperFullPreparationReference.width GeneralPaperReferenceCapacity.referenceWord
  change Tight (fun p => 4*binaryWordWidth (reserve model C d 1 p)+
    (GeneralPaperFastDriverReference.width C d (source model p)+binaryWordWidth (p.n+1)+1+binaryWordWidth (accuracySize p+1))) (logarithm model)
  fun_prop (config := {maxSteps := 4000})

theorem word_positive (model : RationalCostModel) (C d : ℕ) (p : Problem) : 1≤word model C d p :=
  GeneralPaperFullPreparationReference.positive model C d (accuracySize p) (exponent p) (originalSize p)
    (prepared model p).Qv (ledger p) (height model p) (reduced model p) (source model p)

theorem capacity (model : RationalCostModel) (C d : ℕ) (p : Problem) :
    reserve model C d (word model C d p) p<2^(word model C d p) :=
  GeneralPaperFullPreparationReference.capacity model C d (accuracySize p) (exponent p) (originalSize p)
    (prepared model p).Qv (ledger p) (height model p) (reduced model p) (source model p)

end Blotto.GeneralPaperNativeResourceReferenceGrowth
