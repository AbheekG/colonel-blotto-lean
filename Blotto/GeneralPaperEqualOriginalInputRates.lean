import Blotto.GeneralPaperEqualUniformRateAlgebra

/-! Sharp uniform rates on actual original equal-budget inputs, including
accuracy and measured reference construction. The common word is constructed
by the checked initializer. No growth-family matching hypothesis is supplied.
Initializer every-cursor space and preparation/draw representation stay separate. -/
namespace Blotto.GeneralPaperEqualOriginalInputRates
open GeneralPaperEqualResourceDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

theorem ledger_positive {model : RationalCostModel} (p : Problem model) : 1 ≤ ledger p := by unfold ledger; omega

@[fun_prop]
theorem value_bound (model : RationalCostModel) :
    Bound (fun p : Problem model => GeneralPaperValueRoundingInputPrice.inputSize p.values) ledger logarithm :=
  pointwise _ _ _ 1 (fun p => by dsimp [ledger, originalSize]; omega)

@[fun_prop]
theorem budget_bound (model : RationalCostModel) :
    Bound (fun p : Problem model => rationalWordWidth p.budget) ledger logarithm :=
  pointwise _ _ _ 1 (fun p => by dsimp [ledger, budgetSize]; omega)

@[fun_prop]
theorem accuracy_bound (model : RationalCostModel) : Bound (accuracySize (model := model)) ledger logarithm :=
  pointwise _ _ _ 1 (fun p => by dsimp [ledger]; omega)

@[fun_prop]
theorem count_bound (model : RationalCostModel) : Bound (fun p : Problem model => p.n) ledger logarithm :=
  pointwise _ _ _ 1 (fun p => by dsimp [ledger]; omega)

@[fun_prop]
theorem value_small (model : RationalCostModel) :
    Small (fun p : Problem model => GeneralPaperValueRoundingInputPrice.inputSize p.values) logarithm :=
  GeneralPaperEqualResourceDomain.original_small model

@[fun_prop]
theorem original_budget_small (model : RationalCostModel) : Small (fun p : Problem model => rationalWordWidth p.budget) logarithm :=
  GeneralPaperEqualResourceDomain.budget_small model

@[fun_prop]
theorem exponent_small (model : RationalCostModel) : Small (fun p : Problem model => p.k) logarithm :=
  small_of_tight (exponent_tight model) logarithm_positive

@[fun_prop]
theorem exponent_polylog (model : RationalCostModel) : Polylog (fun p : Problem model => p.k) logarithm :=
  polylog_of_tight (exponent_tight model)

@[fun_prop]
theorem exponent_bound (model : RationalCostModel) : Bound (fun p : Problem model => p.k) ledger logarithm :=
  rate_mono (exponent_polylog model) ledger_positive

@[fun_prop]
theorem dyadic_small (model : RationalCostModel) : Small (fun p : Problem model => 2 ^ p.k) logarithm :=
  power_two_small _ _ logarithm_positive (exponent_tight model)

@[fun_prop]
theorem common_word_polylog (model : RationalCostModel) (K : ℕ) :
    Polylog (GeneralPaperEqualCommonReference.word K (model := model)) logarithm :=
  polylog_of_tight (GeneralPaperEqualCommonReference.word_tight K model)

@[fun_prop]
theorem common_word_bound (model : RationalCostModel) (K : ℕ) :
    Bound (GeneralPaperEqualCommonReference.word K (model := model)) ledger logarithm :=
  rate_mono (common_word_polylog model K) ledger_positive

@[fun_prop]
theorem common_word_small (model : RationalCostModel) (K : ℕ) :
    Small (GeneralPaperEqualCommonReference.word K (model := model)) logarithm :=
  small_of_tight (GeneralPaperEqualCommonReference.word_tight K model) logarithm_positive

@[fun_prop]
theorem groups_polylog (model : RationalCostModel) : Polylog (groups (model := model)) logarithm :=
  dominated (polylog_constant 3 logarithm) (fun p => GeneralPaperEqualNativeCache.group_count (rounded p) p.small)

@[fun_prop]
theorem segments_polylog (model : RationalCostModel) : Polylog (segments (model := model)) logarithm :=
  dominated (polylog_constant 7 logarithm) (fun p => (GeneralPaperEqualNativeCache.compact_count (rounded p) p.small).2)

@[fun_prop]
theorem width_polylog (model : RationalCostModel) : Polylog (width (model := model)) logarithm := by
  have hL : ∀ p : Problem model, 1 ≤ logarithm p := logarithm_positive
  have hCap : Polylog (fun p : Problem model => 3670016 * (binaryWordWidth p.n + p.k + 10) + 1) logarithm := by fun_prop
  exact dominated hCap (fun p => GeneralPaperEqualNativeCache.rangeBits true model 1 p.k p.values p.selector p.correct p.small p.budget)

def bitPrice (model : RationalCostModel) (K : ℕ) (p : Problem model) : ℕ :=
  let W := GeneralPaperEqualCommonReference.word K p
  GeneralPaperEqualBitPreparationLedger.profile model W W p.k p.values (rationalWordWidth p.budget)

theorem bit_price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (bitPrice model K) ledger logarithm := by
  have hL : ∀ p : Problem model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Problem model, 1 ≤ ledger p := ledger_positive
  unfold bitPrice
  simp only [GeneralPaperEqualBitPreparationRates.ledger_eq]
  dsimp only [GeneralPaperEqualBitPreparationRates.profile, GeneralPaperEqualBitPreparationRates.aggregate,
    GeneralPaperValueRoundingPaperContract.scaleBitProfile, GeneralPaperValueRoundingPaperContract.scale,
    GeneralPaperSummaryArrayExecution.arrayWord, GeneralPaperEqualLengthArray.height, expressionHeightBudget,
    GeneralPaperEqualPackingExecution.unit, GeneralPaperNatPowerOperands.width,
    GeneralPaperNaturalPrimitivePrice.binary, GeneralPaperNaturalPrimitivePrice.word]
  fun_prop (config := {maxSteps := 50000})

def sourceWork (model : RationalCostModel) (K : ℕ) (p : Problem model) : ℕ :=
  let W := GeneralPaperEqualCommonReference.word K p
  let result := (GeneralPaperEqualAddressedPreparation.run true model W W p.k p.values p.selector p.correct
    (small_at_reference p W) p.budget).2
  GeneralPaperEqualBitPreparationLedger.total result.1.1 result.1.2.1 result.1.2.2 result.2.1 result.2.2.1 result.2.2.2

theorem source_work_bound (model : RationalCostModel) (K : ℕ) (p : Problem model) : sourceWork model K p ≤ bitPrice model K p :=
  GeneralPaperEqualBitPreparationLedger.bit_work model _ _ p.k p.values p.selector p.correct (small_at_reference p _) p.budget

theorem source_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (sourceWork model K) ledger logarithm := dominated (bit_price_rate model hFast K) (source_work_bound model K)


theorem initialization_price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Problem model => GeneralPaperEqualCommonReference.initializationPrice model
      (GeneralPaperEqualCommonReference.word K p) K p) ledger logarithm := by
  have hL : ∀ p : Problem model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Problem model, 1 ≤ ledger p := ledger_positive
  dsimp only [GeneralPaperEqualCommonReference.initializationPrice,
    GeneralPaperEqualReferenceConstruction.measuredProfile, GeneralPaperValueInputWordLength.profile,
    GeneralPaperValueInputWordLength.unit, GeneralPaperWordLengthLifetime.rationalProfile,
    GeneralPaperEqualReferenceConstruction.profile, GeneralPaperEqualReferenceConstruction.cap,
    GeneralPaperBinaryAccuracyConstructionStorage.price, GeneralPaperAccuracyCountConstructionStorage.price,
    GeneralPaperAccuracyCountConstructionStorage.step, GeneralPaperAccuracyCountConstructionStorage.width,
    GeneralPaperEqualRouteConstruction.indicesWork, originalSize, budgetSize]
  fun_prop (config := {maxSteps := 50000})

def totalPrice (model : RationalCostModel) (K : ℕ) (p : Problem model) : ℕ :=
  GeneralPaperEqualCommonReference.initializationPrice model (GeneralPaperEqualCommonReference.word K p) K p + bitPrice model K p

def totalWork (model : RationalCostModel) (K : ℕ) (p : Problem model) : ℕ :=
  (GeneralPaperEqualCommonReference.prepareReference model (GeneralPaperEqualCommonReference.word K p) K p).2 + sourceWork model K p

theorem total_work_bound (model : RationalCostModel) (K : ℕ) (p : Problem model) : totalWork model K p ≤ totalPrice model K p :=
  Nat.add_le_add (GeneralPaperEqualCommonReference.initialization_work model _ K p) (source_work_bound model K p)

theorem total_price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (totalPrice model K) ledger logarithm :=
  bound_add _ _ ledger logarithm logarithm_positive (initialization_price_rate model hFast K) (bit_price_rate model hFast K)

theorem total_work_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (totalWork model K) ledger logarithm := dominated (total_price_rate model hFast K) (total_work_bound model K)


theorem reserve_at_one_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Bound (GeneralPaperEqualCommonReference.reserve model 1) ledger logarithm := by
  have hL : ∀ p : Problem model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Problem model, 1 ≤ ledger p := ledger_positive
  unfold GeneralPaperEqualCommonReference.reserve
  dsimp only [
    GeneralPaperBinaryAccuracyConstructionStorage.profile,
    GeneralPaperBinaryAccuracyConstructionStorage.cap,
    GeneralPaperBinaryAccuracyConstructionStorage.price,
    GeneralPaperAccuracyCountConstructionStorage.profile,
    GeneralPaperAccuracyCountConstructionStorage.frameProfile,
    GeneralPaperAccuracyCountConstructionStorage.cap,
    GeneralPaperAccuracyCountConstructionStorage.price,
    GeneralPaperAccuracyCountConstructionStorage.step,
    GeneralPaperAccuracyCountConstructionStorage.width,
    GeneralPaperBooleanRulerWorkStorage.profile,
    GeneralPaperBooleanRulerWorkStorage.budget,
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
    GeneralPaperPackingAllocationLifetime.indicesProfile,
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
    GeneralPaperWordLengthLifetime.rationalProfile,
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
    GeneralPaperPositiveScanLifetime.labelProfile,
    GeneralPaperPreparedPositiveLabels.bound,
    GeneralPaperEqualRouteConstruction.indicesWork,
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
    GeneralPaperIndexedArrayLifetime.frame,
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
    expressionHeightBudget]
  fun_prop (config := {maxSteps := 50000})

theorem reserve_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) (hK : 1 ≤ K) :
    Bound (fun p : Problem model => GeneralPaperEqualCommonReference.reserve model
      (GeneralPaperEqualCommonReference.word K p) p) ledger logarithm :=
  profile_at_word (GeneralPaperEqualCommonReference.reserve model) (GeneralPaperEqualCommonReference.word K)
    ledger logarithm (GeneralPaperEqualCommonReference.reserve_scaling model)
    (GeneralPaperEqualCommonReference.word_positive K hK) (GeneralPaperEqualCommonReference.word_tight K model)
    (reserve_at_one_rate model hFast)

/-- One global arithmetic-model constant supplies both actual initialization
and native preparation words. The space statement covers the defined native
post-initializer phases, with accuracy retained; initializer cursors are separate. -/
theorem time_space_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es : ℕ, 1 ≤ K ∧ ∀ p : Problem model,
      let W := GeneralPaperEqualCommonReference.word K p
      let initial := GeneralPaperEqualCommonReference.prepareReference model W K p
      initial.1.1 = p.k ∧ initial.1.2 = W ∧ totalWork model K p ≤ At * ledger p * (logarithm p) ^ et ∧
      ∀ phase : GeneralPaperEqualCommonReference.Phase model W p,
        GeneralPaperEqualCommonReference.window model W p phase ≤ As * ledger p * (logarithm p) ^ es ∧
        GeneralPaperEqualCommonReference.window model W p phase < 2 ^ W := by
  obtain ⟨K, hK, hSafe⟩ := GeneralPaperEqualCommonReference.uniform_capacity model hFast
  obtain ⟨At, et, hTime⟩ := total_work_rate model hFast K
  obtain ⟨As, es, hSpace⟩ := reserve_rate model hFast K hK
  refine ⟨K, At, et, As, es, hK, fun p => ?_⟩
  refine ⟨GeneralPaperEqualCommonReference.initialized_exponent model _ K p,
    GeneralPaperEqualCommonReference.initialized_word model _ K p, hTime p, fun phase => ?_⟩
  have h := GeneralPaperEqualCommonReference.native_window_bound model (GeneralPaperEqualCommonReference.word K p) p phase
  exact ⟨h.trans (hSpace p), h.trans_lt (hSafe p)⟩

end Blotto.GeneralPaperEqualOriginalInputRates
