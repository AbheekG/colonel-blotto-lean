import Blotto.GeneralPaperEqualInitializerLifetime

/-! Initializer and native preparation share one uniform constructed word.
The generic self-reference capacity lemma includes sizing costs/counters;
all extended-family word bounds are erased analysis of actual source data. -/
namespace Blotto.GeneralPaperEqualFullInitializationResources
open GeneralPaperEqualResourceDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra GeneralPaperEqualOriginalInputRates
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def profile (model : RationalCostModel) (W K : ℕ) (p : Problem model) : ℕ :=
  GeneralPaperEqualInitializerLifetime.profile model W K p + GeneralPaperEqualCommonReference.reserve model W p

def Phase (model : RationalCostModel) (W : ℕ) (p : Problem model) :=
  Sum (GeneralPaperEqualInitializerLifetime.Phase p.n) (GeneralPaperEqualCommonReference.Phase model W p)

def window (model : RationalCostModel) (W K : ℕ) (p : Problem model) : Phase model W p → ℕ
  | .inl phase => GeneralPaperEqualInitializerLifetime.window model W K p phase
  | .inr phase => GeneralPaperEqualInitializerLifetime.returnedOwner model W K p + GeneralPaperEqualCommonReference.window model W p phase

theorem all_phases (model : RationalCostModel) (W K : ℕ) (p : Problem model) (phase : Phase model W p) :
    window model W K p phase ≤ profile model W K p := by
  have hReturn := GeneralPaperEqualInitializerLifetime.all_phases model W K p .returned
  simp only [GeneralPaperEqualInitializerLifetime.window, GeneralPaperEqualInitializerLifetime.cursorControls,
    GeneralPaperEqualInitializerLifetime.component] at hReturn
  cases phase with
  | inl phase =>
    exact (GeneralPaperEqualInitializerLifetime.all_phases model W K p phase).trans (Nat.le_add_right _ _)
  | inr phase =>
    have hNative := GeneralPaperEqualCommonReference.native_window_bound model W p phase
    change GeneralPaperEqualInitializerLifetime.returnedOwner model W K p + GeneralPaperEqualCommonReference.window model W p phase ≤ _
    unfold profile
    omega

structure Parameters (model : RationalCostModel) where
  input : Problem model
  reference : ℕ
  coefficient : ℕ

def logarithmicMeasure {model : RationalCostModel} (a : Parameters model) : ℕ :=
  logarithm a.input + binaryWordWidth a.reference + binaryWordWidth a.coefficient

theorem measure_positive {model : RationalCostModel} (a : Parameters model) : 1 ≤ logarithmicMeasure a := by
  have h := logarithm_positive a.input
  dsimp only [logarithmicMeasure]
  omega

theorem lift_small (model : RationalCostModel) (f : Problem model → ℕ) (hf : Small f logarithm) :
    Small (fun a : Parameters model => f a.input) logarithmicMeasure := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, fun a => ?_⟩
  exact (hC a.input).trans (Nat.mul_le_mul_left C (by dsimp only [logarithmicMeasure]; omega))

theorem lift_tight (model : RationalCostModel) (f : Problem model → ℕ) (hf : Tight f logarithm) :
    Tight (fun a : Parameters model => f a.input) logarithmicMeasure := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, fun a => ?_⟩
  exact (hC a.input).trans (Nat.mul_le_mul_left C (by dsimp only [logarithmicMeasure]; omega))

theorem uniform_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Problem model) (W K : ℕ),
      binaryWordWidth (profile model W K p) ≤ C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  have hL : ∀ a : Parameters model, 1 ≤ logarithmicMeasure a := measure_positive
  have hS := lift_small model originalSize (GeneralPaperEqualResourceDomain.original_small model)
  have hSRaw : Small (fun a : Parameters model => GeneralPaperValueRoundingInputPrice.inputSize a.input.values) logarithmicMeasure := hS
  have hb := lift_small model budgetSize (GeneralPaperEqualResourceDomain.budget_small model)
  have hbRaw : Small (fun a : Parameters model => rationalWordWidth a.input.budget) logarithmicMeasure := hb
  have hE := lift_small model accuracySize (GeneralPaperEqualResourceDomain.accuracy_small model)
  have hn := lift_small model (fun p => p.n) (GeneralPaperEqualResourceDomain.count_small model)
  have hk := lift_tight model (fun p => p.k) (GeneralPaperEqualResourceDomain.exponent_tight model)
  have hkSmall := small_of_tight hk hL
  have hm := lift_small model groups (GeneralPaperEqualResourceDomain.groups_small model)
  have hc := lift_small model segments (GeneralPaperEqualResourceDomain.segments_small model)
  have hw := lift_small model width (GeneralPaperEqualResourceDomain.width_small model)
  have hW : Small (fun a : Parameters model => a.reference) logarithmicMeasure := by
    refine ⟨1, fun a => ?_⟩
    dsimp only [logarithmicMeasure]
    omega
  have hK : Small (fun a : Parameters model => a.coefficient) logarithmicMeasure := by
    refine ⟨1, fun a => ?_⟩
    dsimp only [logarithmicMeasure]
    omega
  have hBase : Tight (fun a : Parameters model => logarithm a.input) logarithmicMeasure :=
    ⟨1, fun a => by dsimp only [logarithmicMeasure]; omega⟩
  have hBaseSmall := small_of_tight hBase hL
  have hReturned : Small (fun a : Parameters model => GeneralPaperEqualCommonReference.word a.coefficient a.input) logarithmicMeasure := by
    unfold GeneralPaperEqualCommonReference.word
    fun_prop
  have hShort : Tight (fun a : Parameters model => binaryWordWidth a.input.n + a.input.k + 9) logarithmicMeasure := by fun_prop
  have hDen : Small (fun a : Parameters model => GeneralPaperEqualNativeSampler.roundDen true model a.reference a.input.k a.input.values) logarithmicMeasure := by
    obtain ⟨C, hC⟩ := hShort
    exact ⟨C, fun a => (GeneralPaperEqualNativeSampler.roundDen_word true model a.reference a.input.k
      a.input.values a.input.selector a.input.correct).trans (hC a)⟩
  have hAll : Small (fun a : Parameters model => profile model a.reference a.coefficient a.input) logarithmicMeasure := by
    unfold profile
    dsimp only [GeneralPaperEqualCommonReference.reserve,
      GeneralPaperEqualPreparationLifetime.profile,
      GeneralPaperEqualRouteCallerLifetime.profile,
      GeneralPaperRouteConstructionLifetime.profile,
      GeneralPaperRouteConstructionLifetime.controlProfile,
      GeneralPaperRouteTableLifetime.profile,
      GeneralPaperRouteGroupFrames.profile,
      GeneralPaperRouteGroupFrames.frameProfile,
      GeneralPaperRouteMemberFrames.frameProfile,
      GeneralPaperEqualPackingCapacity.profile,
      GeneralPaperEqualPackingCallerLifetime.profile,
      GeneralPaperPackingLifetime.profile,
      GeneralPaperPackingFrameLifetime.frameProfile,
      GeneralPaperPackingAllocationLifetime.poolProfile,
      GeneralPaperEqualInitialPrefixCapacity.profile,
      GeneralPaperEqualFinalClosureCapacity.profile,
      GeneralPaperEqualFinalClosureCaller.profile,
      GeneralPaperEqualFinalClosureCaller.borrowedProfile,
      GeneralPaperEqualFinalClosureCaller.workProfile,
      GeneralPaperEqualNativeRetainedStorage.profile,
      GeneralPaperEqualNativeRetainedStorage.height,
      GeneralPaperEqualNativeRetainedStorage.short,
      GeneralPaperEqualRetainedStorage.preparedProfile,
      GeneralPaperEqualBitDrawRates.log,
      GeneralPaperEqualBitDrawRates.word,
      GeneralPaperEqualBitDrawRates.size,
      GeneralPaperEqualFinalClosureLifetime.profile,
      GeneralPaperEqualFinalClosureLifetime.controlProfile,
      GeneralPaperEqualFinalClosureLifetime.time,
      GeneralPaperAddressConstructionLifetime.profile,
      GeneralPaperEqualAddressConstruction.operandWidth,
      GeneralPaperEqualBooleanCapacity.profile,
      GeneralPaperEqualBooleanCallerLifetime.profile,
      GeneralPaperBooleanCacheLifetime.profile,
      GeneralPaperBooleanCacheLifetime.rulerProfile,
      GeneralPaperBooleanCacheLifetime.labelsProfile,
      GeneralPaperBooleanCacheLifetime.controlProfile,
      GeneralPaperStoredBooleanCache.bound,
      GeneralPaperBooleanRowsLifetime.profile,
      GeneralPaperBooleanRowsLifetime.listProfile,
      GeneralPaperBooleanRowsLifetime.entryProfile,
      GeneralPaperBooleanRowsLifetime.localProfile,
      GeneralPaperBooleanRowsLifetime.time,
      GeneralPaperStoredBooleanCache.rowBound,
      GeneralPaperWordEncodingLifetime.windowProfile,
      GeneralPaperWordEncodingLifetime.profile,
      GeneralPaperWordEncodingLifetime.bitListProfile,
      GeneralPaperWordEncodingLifetime.time,
      GeneralPaperStoredWordEncoding.stepBound,
      GeneralPaperEqualRetainedStorage.cacheProfile,
      GeneralPaperEqualRetainedStorage.wordProfile,
      GeneralPaperEqualPowerWidthCapacity.profile,
      GeneralPaperEqualPowerWidthCaller.profile,
      GeneralPaperEqualPowerWidthLifetime.profile,
      GeneralPaperEqualPowerWidthLifetime.controlProfile,
      GeneralPaperEqualPowerWidthLifetime.controlCap,
      GeneralPaperEqualPowerWidthLifetime.widthTime,
      GeneralPaperEqualPowerWidthLifetime.cachedPowerProfile,
      GeneralPaperPowerCeilingStorage.profile,
      GeneralPaperPowerCeilingStorage.frameProfile,
      GeneralPaperPowerCeilingStorage.metadataCap,
      GeneralPaperPowerCeilingStorage.price,
      GeneralPaperEqualMiddlePreparationLifetime.profile,
      GeneralPaperEqualIntegerCallerLifetime.profile,
      GeneralPaperCategoricalIntegerLifetime.profile,
      GeneralPaperCategoricalIntegerLifetime.totalTime,
      GeneralPaperCategoricalIntegerLifetime.arrayTime,
      GeneralPaperCategoricalIntegerLifetime.productOwnerProfile,
      GeneralPaperCategoricalIntegerLifetime.productTime,
      GeneralPaperStoredCategoricalProduct.stepBound,
      GeneralPaperStoredCategoricalCounts.stepBound,
      GeneralPaperEqualCompactionCallerLifetime.profile,
      GeneralPaperEqualIntegerCallerLifetime.residentProfile,
      GeneralPaperEqualNativeSampler.segmentHeight,
      GeneralPaperEqualRetainedStorage.segmentProfile,
      GeneralPaperCompactionLifetime.profile,
      GeneralPaperCompactionLifetime.controlProfile,
      GeneralPaperPreparedSegmentCompaction.bound,
      GeneralPaperPreparedSegmentCompaction.makeBound,
      GeneralPaperCompactionArrayLifetime.residentProfile,
      GeneralPaperCompactionArrayLifetime.ownerProfile,
      GeneralPaperCompactionArrayLifetime.arrayTime,
      GeneralPaperCompactionArrayLifetime.selectionProfile,
      GeneralPaperCompactionCallbackLifetime.profile,
      GeneralPaperPreparedSegmentCompaction.itemBound,
      GeneralPaperCompactionCallbackLifetime.lookupProfile,
      GeneralPaperPositiveSelectionLifetime.profile,
      GeneralPaperPreparedPositiveLabels.bound,
      GeneralPaperPositiveLabelScan.stepBound,
      GeneralPaperEqualSegmentCallerLifetime.profile,
      GeneralPaperEqualSegmentCallerLifetime.ownerProfile,
      GeneralPaperEqualBitPreparationLedger.profile,
      GeneralPaperEqualPackingExecution.unit,
      GeneralPaperValueRoundingInputPrice.size,
      GeneralPaperValueRoundingPaperContract.scaleBitProfile,
      GeneralPaperNaturalPrimitivePrice.binary,
      GeneralPaperNaturalPrimitivePrice.word,
      GeneralPaperEqualSegmentCallerOwners.profile,
      GeneralPaperEqualSegmentCallerOwners.controlProfile,
      GeneralPaperEqualStaticCodeOwner.profile,
      GeneralPaperExpressionCodeOwner.unit,
      GeneralPaperEqualRouteOwner.profile,
      GeneralPaperEqualPackedOwner.profile,
      GeneralPaperEqualNativeSampler.fieldHeight,
      GeneralPaperNativeSegmentFactoryLifetime.profile,
      GeneralPaperNativeSegmentFactoryLifetime.selectorProfile,
      GeneralPaperUniformSegmentPreparation.bound,
      GeneralPaperThreeSegmentPreparation.bound,
      GeneralPaperPairSegmentPreparation.bound,
      GeneralPaperFixedSegmentFactoryLifetime.profile,
      GeneralPaperFixedSegmentFactoryLifetime.controlProfile,
      GeneralPaperFixedSegmentFactoryLifetime.cap,
      GeneralPaperSegmentCompilerLifetime.profile,
      GeneralPaperSegmentCompilerStorage.matrixOwnerProfile,
      GeneralPaperSegmentCompilerStorage.rowOwnerProfile,
      GeneralPaperSegmentCompilerStorage.assemblyProfile,
      GeneralPaperSegmentCompilerStorage.compilerTime,
      GeneralPaperSegmentExpressionCompiler.bound,
      GeneralPaperExpressionArrayReturns.matrixProfile,
      GeneralPaperExpressionMatrixLifetime.activeProfile,
      GeneralPaperExpressionMatrixLifetime.outerProfile,
      GeneralPaperExpressionMatrixLifetime.matrixTime,
      GeneralPaperExpressionArrayReturns.rowProfile,
      GeneralPaperExpressionRowLifetime.profile,
      GeneralPaperExpressionRowLifetime.rowTime,
      GeneralPaperExpressionRowLifetime.callbackTime,
      GeneralPaperExpressionBitExecution.nodeBound,
      GeneralPaperExpressionBitExecution.unit,
      GeneralPaperFixedEnvironmentLifetime.profile,
      GeneralPaperFixedEnvironmentLifetime.time,
      GeneralPaperEqualInitialPrefixLifetime.profile,
      GeneralPaperEqualInitialPrefixLifetime.roundedProfile,
      GeneralPaperEqualPrefixOwners.roundedProfile,
      GeneralPaperEqualInitialPrefixLifetime.inputProfile,
      GeneralPaperEqualInitialPrefixLifetime.roundingTime,
      GeneralPaperEqualLengthReturnStorage.profile,
      GeneralPaperEqualLengthPhaseStorage.profile,
      GeneralPaperEqualLengthPhaseStorage.loopProfile,
      GeneralPaperEqualLengthArray.height,
      GeneralPaperEqualDenominatorLifetime.profile,
      GeneralPaperNativeScaleConstructionStorage.roundingProfile,
      GeneralPaperNativeScaleConstructionStorage.roundingCap,
      GeneralPaperNativeScaleConstructionStorage.roundingPrice,
      GeneralPaperNativeScaleConstructionStorage.profile,
      GeneralPaperNativeScaleConstructionStorage.cap,
      GeneralPaperNativeScaleConstructionStorage.price,
      GeneralPaperOriginalSourceValuePrice.scalePrice,
      GeneralPaperOriginalSourceValuePrice.scaleWidth,
      GeneralPaperNatPowerBitConstructionStorage.profile,
      GeneralPaperNatPowerBitConstructionStorage.frameProfile,
      GeneralPaperNatPowerBitConstructionStorage.cap,
      GeneralPaperNatPowerBitConstructionStorage.price,
      GeneralPaperNatPowerOperands.width,
      GeneralPaperNatPowerConstructionStorage.payload,
      GeneralPaperValueRoundingPaperContract.scale,
      GeneralPaperValueWeightSumConstructionStorage.driverProfile,
      GeneralPaperValueWeightSumConstructionStorage.driverPrice,
      GeneralPaperValueWeightSumConstructionStorage.profile,
      GeneralPaperValueWeightSumConstructionStorage.frameProfile,
      GeneralPaperValueWeightSumConstructionStorage.cap,
      GeneralPaperValueWeightSumConstructionStorage.price,
      GeneralPaperEncodedBasisStorage.arrayProfile,
      GeneralPaperOriginalValueRoundConstructionStorage.profile,
      GeneralPaperOriginalValueRoundConstructionStorage.cap,
      GeneralPaperOriginalValueRoundConstructionStorage.callbackProfile,
      GeneralPaperOriginalValueRoundConstructionStorage.scalarProfile,
      GeneralPaperPositiveCeilingConstructionStorage.profile,
      GeneralPaperPositiveCeilingConstructionStorage.price,
      GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice,
      GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice,
      GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth,
      GeneralPaperSummaryArrayExecution.arrayWord,
      GeneralPaperNativePayloadFillStorage.profile,
      GeneralPaperNativePayloadFillStorage.frameProfile,
      GeneralPaperNativePayloadFillStorage.metadataCap,
      GeneralPaperNativePayloadFillStorage.workCap,
      GeneralPaperEqualInitializerLifetime.profile,
      GeneralPaperEqualInitializerLifetime.scratchProfile,
      GeneralPaperEqualInitializerLifetime.returnedProfile,
      GeneralPaperEqualInitializerLifetime.sumProfile,
      GeneralPaperEqualReferenceWordLifetime.profile,
      GeneralPaperValueInputLengthLifetime.profile,
      GeneralPaperValueInputLengthLifetime.frameProfile,
      GeneralPaperPackingAllocationLifetime.indicesProfile,
      GeneralPaperIndexedArrayLifetime.frame,
      GeneralPaperPositiveScanLifetime.labelProfile,
      GeneralPaperBinaryAccuracyConstructionStorage.profile,
      GeneralPaperBinaryAccuracyConstructionStorage.cap,
      GeneralPaperAccuracyCountConstructionStorage.profile,
      GeneralPaperAccuracyCountConstructionStorage.frameProfile,
      GeneralPaperAccuracyCountConstructionStorage.cap,
      GeneralPaperBooleanRulerWorkStorage.profile,
      GeneralPaperBooleanRulerWorkStorage.budget,
      GeneralPaperEqualInitializerLifetime.cursorProfile,
      GeneralPaperEqualInitializerLifetime.controlProfile,
      GeneralPaperEqualInitializerLifetime.controlCap,
      GeneralPaperEqualCommonReference.initializationPrice,
      GeneralPaperEqualReferenceConstruction.measuredProfile,
      GeneralPaperEqualReferenceConstruction.profile,
      GeneralPaperEqualReferenceConstruction.cap,
      GeneralPaperWordLengthLifetime.rationalProfile,
      GeneralPaperValueInputWordLength.profile,
      GeneralPaperValueInputWordLength.unit,
      GeneralPaperEqualRouteConstruction.indicesWork,
      GeneralPaperBinaryAccuracyConstructionStorage.price,
      GeneralPaperAccuracyCountConstructionStorage.price,
      GeneralPaperAccuracyCountConstructionStorage.step,
      GeneralPaperAccuracyCountConstructionStorage.width,
      GeneralPaperEqualInitializerLifetime.inputProfile,
      expressionHeightBudget]
    fun_prop (config := {maxSteps := 50000})
  obtain ⟨C, hC⟩ := hAll
  exact ⟨C, fun p W K => hC ⟨p, W, K⟩⟩

theorem uniform_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : Problem model,
      profile model (GeneralPaperEqualCommonReference.word K p) K p < 2 ^ GeneralPaperEqualCommonReference.word K p :=
  GeneralPaperSelfReferenceCapacity.uniform_capacity (profile model) logarithm logarithm_positive (uniform_word_growth model hFast)


theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Problem model => profile model (GeneralPaperEqualCommonReference.word K p) K p) ledger logarithm := by
  have hL : ∀ p : Problem model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Problem model, 1 ≤ ledger p := GeneralPaperEqualOriginalInputRates.ledger_positive
  have hOriginal : Bound (originalSize (model := model)) ledger logarithm := GeneralPaperEqualOriginalInputRates.value_bound model
  have hBudget : Bound (budgetSize (model := model)) ledger logarithm := GeneralPaperEqualOriginalInputRates.budget_bound model
  have hShort : Tight (fun p : Problem model => binaryWordWidth p.n + p.k + 9) logarithm := by fun_prop
  have hDen : Small (fun p : Problem model => GeneralPaperEqualNativeSampler.roundDen true model
      (GeneralPaperEqualCommonReference.word K p) p.k p.values) logarithm := by
    obtain ⟨C, hC⟩ := hShort
    exact ⟨C, fun p => (GeneralPaperEqualNativeSampler.roundDen_word true model
      (GeneralPaperEqualCommonReference.word K p) p.k p.values p.selector p.correct).trans (hC p)⟩
  unfold profile
  dsimp only [GeneralPaperEqualCommonReference.reserve,
    GeneralPaperEqualPreparationLifetime.profile,
    GeneralPaperEqualRouteCallerLifetime.profile,
    GeneralPaperRouteConstructionLifetime.profile,
    GeneralPaperRouteConstructionLifetime.controlProfile,
    GeneralPaperRouteTableLifetime.profile,
    GeneralPaperRouteGroupFrames.profile,
    GeneralPaperRouteGroupFrames.frameProfile,
    GeneralPaperRouteMemberFrames.frameProfile,
    GeneralPaperEqualPackingCapacity.profile,
    GeneralPaperEqualPackingCallerLifetime.profile,
    GeneralPaperPackingLifetime.profile,
    GeneralPaperPackingFrameLifetime.frameProfile,
    GeneralPaperPackingAllocationLifetime.poolProfile,
    GeneralPaperEqualInitialPrefixCapacity.profile,
    GeneralPaperEqualFinalClosureCapacity.profile,
    GeneralPaperEqualFinalClosureCaller.profile,
    GeneralPaperEqualFinalClosureCaller.borrowedProfile,
    GeneralPaperEqualFinalClosureCaller.workProfile,
    GeneralPaperEqualNativeRetainedStorage.profile,
    GeneralPaperEqualNativeRetainedStorage.height,
    GeneralPaperEqualNativeRetainedStorage.short,
    GeneralPaperEqualRetainedStorage.preparedProfile,
    GeneralPaperEqualBitDrawRates.log,
    GeneralPaperEqualBitDrawRates.word,
    GeneralPaperEqualBitDrawRates.size,
    GeneralPaperEqualFinalClosureLifetime.profile,
    GeneralPaperEqualFinalClosureLifetime.controlProfile,
    GeneralPaperEqualFinalClosureLifetime.time,
    GeneralPaperAddressConstructionLifetime.profile,
    GeneralPaperEqualAddressConstruction.operandWidth,
    GeneralPaperEqualBooleanCapacity.profile,
    GeneralPaperEqualBooleanCallerLifetime.profile,
    GeneralPaperBooleanCacheLifetime.profile,
    GeneralPaperBooleanCacheLifetime.rulerProfile,
    GeneralPaperBooleanCacheLifetime.labelsProfile,
    GeneralPaperBooleanCacheLifetime.controlProfile,
    GeneralPaperStoredBooleanCache.bound,
    GeneralPaperBooleanRowsLifetime.profile,
    GeneralPaperBooleanRowsLifetime.listProfile,
    GeneralPaperBooleanRowsLifetime.entryProfile,
    GeneralPaperBooleanRowsLifetime.localProfile,
    GeneralPaperBooleanRowsLifetime.time,
    GeneralPaperStoredBooleanCache.rowBound,
    GeneralPaperWordEncodingLifetime.windowProfile,
    GeneralPaperWordEncodingLifetime.profile,
    GeneralPaperWordEncodingLifetime.bitListProfile,
    GeneralPaperWordEncodingLifetime.time,
    GeneralPaperStoredWordEncoding.stepBound,
    GeneralPaperEqualRetainedStorage.cacheProfile,
    GeneralPaperEqualRetainedStorage.wordProfile,
    GeneralPaperEqualPowerWidthCapacity.profile,
    GeneralPaperEqualPowerWidthCaller.profile,
    GeneralPaperEqualPowerWidthLifetime.profile,
    GeneralPaperEqualPowerWidthLifetime.controlProfile,
    GeneralPaperEqualPowerWidthLifetime.controlCap,
    GeneralPaperEqualPowerWidthLifetime.widthTime,
    GeneralPaperEqualPowerWidthLifetime.cachedPowerProfile,
    GeneralPaperPowerCeilingStorage.profile,
    GeneralPaperPowerCeilingStorage.frameProfile,
    GeneralPaperPowerCeilingStorage.metadataCap,
    GeneralPaperPowerCeilingStorage.price,
    GeneralPaperEqualMiddlePreparationLifetime.profile,
    GeneralPaperEqualIntegerCallerLifetime.profile,
    GeneralPaperCategoricalIntegerLifetime.profile,
    GeneralPaperCategoricalIntegerLifetime.totalTime,
    GeneralPaperCategoricalIntegerLifetime.arrayTime,
    GeneralPaperCategoricalIntegerLifetime.productOwnerProfile,
    GeneralPaperCategoricalIntegerLifetime.productTime,
    GeneralPaperStoredCategoricalProduct.stepBound,
    GeneralPaperStoredCategoricalCounts.stepBound,
    GeneralPaperEqualCompactionCallerLifetime.profile,
    GeneralPaperEqualIntegerCallerLifetime.residentProfile,
    GeneralPaperEqualNativeSampler.segmentHeight,
    GeneralPaperEqualRetainedStorage.segmentProfile,
    GeneralPaperCompactionLifetime.profile,
    GeneralPaperCompactionLifetime.controlProfile,
    GeneralPaperPreparedSegmentCompaction.bound,
    GeneralPaperPreparedSegmentCompaction.makeBound,
    GeneralPaperCompactionArrayLifetime.residentProfile,
    GeneralPaperCompactionArrayLifetime.ownerProfile,
    GeneralPaperCompactionArrayLifetime.arrayTime,
    GeneralPaperCompactionArrayLifetime.selectionProfile,
    GeneralPaperCompactionCallbackLifetime.profile,
    GeneralPaperPreparedSegmentCompaction.itemBound,
    GeneralPaperCompactionCallbackLifetime.lookupProfile,
    GeneralPaperPositiveSelectionLifetime.profile,
    GeneralPaperPreparedPositiveLabels.bound,
    GeneralPaperPositiveLabelScan.stepBound,
    GeneralPaperEqualSegmentCallerLifetime.profile,
    GeneralPaperEqualSegmentCallerLifetime.ownerProfile,
    GeneralPaperEqualBitPreparationLedger.profile,
    GeneralPaperEqualPackingExecution.unit,
    GeneralPaperValueRoundingInputPrice.size,
    GeneralPaperValueRoundingPaperContract.scaleBitProfile,
    GeneralPaperNaturalPrimitivePrice.binary,
    GeneralPaperNaturalPrimitivePrice.word,
    GeneralPaperEqualSegmentCallerOwners.profile,
    GeneralPaperEqualSegmentCallerOwners.controlProfile,
    GeneralPaperEqualStaticCodeOwner.profile,
    GeneralPaperExpressionCodeOwner.unit,
    GeneralPaperEqualRouteOwner.profile,
    GeneralPaperEqualPackedOwner.profile,
    GeneralPaperEqualNativeSampler.fieldHeight,
    GeneralPaperNativeSegmentFactoryLifetime.profile,
    GeneralPaperNativeSegmentFactoryLifetime.selectorProfile,
    GeneralPaperUniformSegmentPreparation.bound,
    GeneralPaperThreeSegmentPreparation.bound,
    GeneralPaperPairSegmentPreparation.bound,
    GeneralPaperFixedSegmentFactoryLifetime.profile,
    GeneralPaperFixedSegmentFactoryLifetime.controlProfile,
    GeneralPaperFixedSegmentFactoryLifetime.cap,
    GeneralPaperSegmentCompilerLifetime.profile,
    GeneralPaperSegmentCompilerStorage.matrixOwnerProfile,
    GeneralPaperSegmentCompilerStorage.rowOwnerProfile,
    GeneralPaperSegmentCompilerStorage.assemblyProfile,
    GeneralPaperSegmentCompilerStorage.compilerTime,
    GeneralPaperSegmentExpressionCompiler.bound,
    GeneralPaperExpressionArrayReturns.matrixProfile,
    GeneralPaperExpressionMatrixLifetime.activeProfile,
    GeneralPaperExpressionMatrixLifetime.outerProfile,
    GeneralPaperExpressionMatrixLifetime.matrixTime,
    GeneralPaperExpressionArrayReturns.rowProfile,
    GeneralPaperExpressionRowLifetime.profile,
    GeneralPaperExpressionRowLifetime.rowTime,
    GeneralPaperExpressionRowLifetime.callbackTime,
    GeneralPaperExpressionBitExecution.nodeBound,
    GeneralPaperExpressionBitExecution.unit,
    GeneralPaperFixedEnvironmentLifetime.profile,
    GeneralPaperFixedEnvironmentLifetime.time,
    GeneralPaperEqualInitialPrefixLifetime.profile,
    GeneralPaperEqualInitialPrefixLifetime.roundedProfile,
    GeneralPaperEqualPrefixOwners.roundedProfile,
    GeneralPaperEqualInitialPrefixLifetime.inputProfile,
    GeneralPaperEqualInitialPrefixLifetime.roundingTime,
    GeneralPaperEqualLengthReturnStorage.profile,
    GeneralPaperEqualLengthPhaseStorage.profile,
    GeneralPaperEqualLengthPhaseStorage.loopProfile,
    GeneralPaperEqualLengthArray.height,
    GeneralPaperEqualDenominatorLifetime.profile,
    GeneralPaperNativeScaleConstructionStorage.roundingProfile,
    GeneralPaperNativeScaleConstructionStorage.roundingCap,
    GeneralPaperNativeScaleConstructionStorage.roundingPrice,
    GeneralPaperNativeScaleConstructionStorage.profile,
    GeneralPaperNativeScaleConstructionStorage.cap,
    GeneralPaperNativeScaleConstructionStorage.price,
    GeneralPaperOriginalSourceValuePrice.scalePrice,
    GeneralPaperOriginalSourceValuePrice.scaleWidth,
    GeneralPaperNatPowerBitConstructionStorage.profile,
    GeneralPaperNatPowerBitConstructionStorage.frameProfile,
    GeneralPaperNatPowerBitConstructionStorage.cap,
    GeneralPaperNatPowerBitConstructionStorage.price,
    GeneralPaperNatPowerOperands.width,
    GeneralPaperNatPowerConstructionStorage.payload,
    GeneralPaperValueRoundingPaperContract.scale,
    GeneralPaperValueWeightSumConstructionStorage.driverProfile,
    GeneralPaperValueWeightSumConstructionStorage.driverPrice,
    GeneralPaperValueWeightSumConstructionStorage.profile,
    GeneralPaperValueWeightSumConstructionStorage.frameProfile,
    GeneralPaperValueWeightSumConstructionStorage.cap,
    GeneralPaperValueWeightSumConstructionStorage.price,
    GeneralPaperEncodedBasisStorage.arrayProfile,
    GeneralPaperOriginalValueRoundConstructionStorage.profile,
    GeneralPaperOriginalValueRoundConstructionStorage.cap,
    GeneralPaperOriginalValueRoundConstructionStorage.callbackProfile,
    GeneralPaperOriginalValueRoundConstructionStorage.scalarProfile,
    GeneralPaperPositiveCeilingConstructionStorage.profile,
    GeneralPaperPositiveCeilingConstructionStorage.price,
    GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice,
    GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice,
    GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth,
    GeneralPaperSummaryArrayExecution.arrayWord,
    GeneralPaperNativePayloadFillStorage.profile,
    GeneralPaperNativePayloadFillStorage.frameProfile,
    GeneralPaperNativePayloadFillStorage.metadataCap,
    GeneralPaperNativePayloadFillStorage.workCap,
    GeneralPaperEqualInitializerLifetime.profile,
    GeneralPaperEqualInitializerLifetime.scratchProfile,
    GeneralPaperEqualInitializerLifetime.returnedProfile,
    GeneralPaperEqualInitializerLifetime.sumProfile,
    GeneralPaperEqualReferenceWordLifetime.profile,
    GeneralPaperValueInputLengthLifetime.profile,
    GeneralPaperValueInputLengthLifetime.frameProfile,
    GeneralPaperPackingAllocationLifetime.indicesProfile,
    GeneralPaperIndexedArrayLifetime.frame,
    GeneralPaperPositiveScanLifetime.labelProfile,
    GeneralPaperBinaryAccuracyConstructionStorage.profile,
    GeneralPaperBinaryAccuracyConstructionStorage.cap,
    GeneralPaperAccuracyCountConstructionStorage.profile,
    GeneralPaperAccuracyCountConstructionStorage.frameProfile,
    GeneralPaperAccuracyCountConstructionStorage.cap,
    GeneralPaperBooleanRulerWorkStorage.profile,
    GeneralPaperBooleanRulerWorkStorage.budget,
    GeneralPaperEqualInitializerLifetime.cursorProfile,
    GeneralPaperEqualInitializerLifetime.controlProfile,
    GeneralPaperEqualInitializerLifetime.controlCap,
    GeneralPaperEqualCommonReference.initializationPrice,
    GeneralPaperEqualReferenceConstruction.measuredProfile,
    GeneralPaperEqualReferenceConstruction.profile,
    GeneralPaperEqualReferenceConstruction.cap,
    GeneralPaperWordLengthLifetime.rationalProfile,
    GeneralPaperValueInputWordLength.profile,
    GeneralPaperValueInputWordLength.unit,
    GeneralPaperEqualRouteConstruction.indicesWork,
    GeneralPaperBinaryAccuracyConstructionStorage.price,
    GeneralPaperAccuracyCountConstructionStorage.price,
    GeneralPaperAccuracyCountConstructionStorage.step,
    GeneralPaperAccuracyCountConstructionStorage.width,
    GeneralPaperEqualInitializerLifetime.inputProfile,
    expressionHeightBudget]
  fun_prop (config := {maxSteps := 50000})

/-- Complete measured initialization and every native preparation phase,
including all reached value/index cursors, use one actual constructed word. -/
theorem time_space_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es : ℕ, 1 ≤ K ∧ ∀ p : Problem model,
      let W := GeneralPaperEqualCommonReference.word K p
      let initial := GeneralPaperEqualCommonReference.prepareReference model W K p
      initial.1.1 = p.k ∧ initial.1.2 = W ∧
      totalWork model K p ≤ At * GeneralPaperEqualResourceHeadline.inputSize p * (GeneralPaperEqualResourceHeadline.paperLog p) ^ et ∧
      ∀ phase : Phase model W p,
        window model W K p phase ≤ As * GeneralPaperEqualResourceHeadline.inputSize p * (GeneralPaperEqualResourceHeadline.paperLog p) ^ es ∧
        window model W K p phase < 2 ^ W := by
  obtain ⟨K, hK, hSafe⟩ := uniform_capacity model hFast
  obtain ⟨At, et, hTime⟩ := GeneralPaperEqualResourceHeadline.bit_time model hFast K
  obtain ⟨As, es, hSpace⟩ := GeneralPaperEqualResourceHeadline.transfer_rate (profile_rate model hFast K)
  refine ⟨K, At, et, As, es, hK, fun p => ?_⟩
  refine ⟨GeneralPaperEqualCommonReference.initialized_exponent model _ K p,
    GeneralPaperEqualCommonReference.initialized_word model _ K p, hTime p, fun phase => ?_⟩
  have h := all_phases model (GeneralPaperEqualCommonReference.word K p) K p phase
  exact ⟨h.trans (hSpace p), h.trans_lt (hSafe p)⟩

end Blotto.GeneralPaperEqualFullInitializationResources
