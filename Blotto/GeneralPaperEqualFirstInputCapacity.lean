import Blotto.GeneralPaperEqualFirstInputResources

/-! One global coefficient covers every actual initializer and corrected
selected phase. Uniform growth includes the computation of the reference
and all full executed price fields; execution only constructs K times the
measured logarithm, without inspecting these erased envelopes. -/
namespace Blotto.GeneralPaperEqualFirstInputCapacity
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

theorem returned_le_profile (model : RationalCostModel) (W K : ℕ) (p : Input model) :
    GeneralPaperEqualInputInitializerLifetime.returnedProfile model W K p ≤
      GeneralPaperEqualInputInitializerLifetime.profile model W K p := by
  unfold GeneralPaperEqualInputInitializerLifetime.profile GeneralPaperEqualInputInitializerLifetime.scratchProfile
  omega

theorem parent_cap_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    {α : Type*} (input : α → Input model) (W K L : α → ℕ) (hL : ∀ x,1 ≤ L x)
    (hW : Small W L) (hK : Small K L) (hn : Small (fun x => (input x).n) L)
    (hk : Tight (fun x => (input x).k) L)
    (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (input x).values) L)
    (hb : Small (fun x => rationalWordWidth (input x).budget) L)
    (hE : Small (fun x => accuracySize (input x)) L) :
    Small (fun x => GeneralPaperEqualFirstInputResources.parentCap model (W x) (K x) (input x)) L := by
  have hkSmall := small_of_tight hk hL
  have hOriginal : Small (fun x => originalSize (input x)) L := hS
  have hBudget : Small (fun x => budgetSize (input x)) L := hb
  dsimp only [
    GeneralPaperEqualInputInitializerLifetime.profile,
    GeneralPaperEqualInputInitializerLifetime.scratchProfile,
    GeneralPaperEqualInputInitializerLifetime.returnedProfile,
    GeneralPaperEqualInputInitializerLifetime.sumProfile,
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
    GeneralPaperEqualInputInitializerLifetime.cursorProfile,
    GeneralPaperEqualInputInitializerLifetime.controlProfile,
    GeneralPaperEqualInputInitializerLifetime.controlCap,
    GeneralPaperEqualInputInitialization.initializationPrice,
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
    GeneralPaperEqualInputInitializerLifetime.inputProfile,
    expressionHeightBudget,
    GeneralPaperEqualFirstPreparationSpace.profile,
    GeneralPaperEqualFirstSegmentCallerSpace.profile,
    GeneralPaperEqualFirstSegmentCallerSpace.ownerProfile,
    GeneralPaperEqualFirstIntegerCallerSpace.compactionProfile,
    GeneralPaperEqualFirstIntegerCallerSpace.profile,
    GeneralPaperEqualFirstIntegerCallerSpace.residentProfile,
    GeneralPaperEqualFirstIntegerCallerSpace.compactionPrice,
    GeneralPaperEqualFirstPowerBooleanSpace.powerProfile,
    GeneralPaperEqualFirstPowerBooleanSpace.profile,
    GeneralPaperEqualFirstFinalClosureSpace.profile,
    GeneralPaperEqualFirstFinalClosureSpace.borrowedProfile,
    GeneralPaperEqualFirstGroupedPreparation.profile,
    GeneralPaperEqualFirstNativeFacts.segmentHeight,
    GeneralPaperEqualFirstNativeFacts.fieldHeight,
    GeneralPaperEqualFirstPrefixRates.segmentBound,
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
    GeneralPaperEqualPackingExecution.unit,
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
    GeneralPaperNatPowerBitConstructionStorage.profile,
    GeneralPaperNatPowerBitConstructionStorage.frameProfile,
    GeneralPaperNatPowerBitConstructionStorage.cap,
    GeneralPaperNatPowerBitConstructionStorage.price,
    GeneralPaperNatPowerOperands.width,
    GeneralPaperNatPowerConstructionStorage.payload,
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
    GeneralPaperSummaryArrayExecution.arrayWord,
    GeneralPaperEqualLengthReturnStorage.profile,
    GeneralPaperEqualLengthPhaseStorage.profile,
    GeneralPaperEqualLengthPhaseStorage.loopProfile,
    GeneralPaperIndexedArrayLifetime.frame,
    GeneralPaperEncodedBasisStorage.arrayProfile,
    GeneralPaperEqualLengthArray.height,
    GeneralPaperEqualDenominatorLifetime.profile,
    expressionHeightBudget,
    GeneralPaperNativeScaleConstructionStorage.roundingProfile,
    GeneralPaperNativeScaleConstructionStorage.roundingCap,
    GeneralPaperNativeScaleConstructionStorage.roundingPrice,
    GeneralPaperNativeScaleConstructionStorage.profile,
    GeneralPaperNativeScaleConstructionStorage.cap,
    GeneralPaperNativeScaleConstructionStorage.price,
    GeneralPaperOriginalSourceValuePrice.scalePrice,
    GeneralPaperOriginalSourceValuePrice.scaleWidth,
    GeneralPaperValueRoundingPaperContract.scale,
    GeneralPaperValueWeightSumConstructionStorage.driverProfile,
    GeneralPaperValueWeightSumConstructionStorage.driverPrice,
    GeneralPaperValueWeightSumConstructionStorage.profile,
    GeneralPaperValueWeightSumConstructionStorage.frameProfile,
    GeneralPaperValueWeightSumConstructionStorage.cap,
    GeneralPaperValueWeightSumConstructionStorage.price,
    GeneralPaperOriginalValueRoundConstructionStorage.profile,
    GeneralPaperOriginalValueRoundConstructionStorage.cap,
    GeneralPaperOriginalValueRoundConstructionStorage.callbackProfile,
    GeneralPaperOriginalValueRoundConstructionStorage.scalarProfile,
    GeneralPaperPositiveCeilingConstructionStorage.profile,
    GeneralPaperPositiveCeilingConstructionStorage.price,
    GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice,
    GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice,
    GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth,
    GeneralPaperNativePayloadFillStorage.profile,
    GeneralPaperNativePayloadFillStorage.frameProfile,
    GeneralPaperNativePayloadFillStorage.metadataCap,
    GeneralPaperNativePayloadFillStorage.workCap,
    GeneralPaperEqualBitScanLifetime.profile,
    GeneralPaperEqualBitScanLifetime.frameProfile,
    GeneralPaperEqualBitScanLifetime.metadataCap,
    GeneralPaperEqualBitScanLifetime.workCap,
    GeneralPaperEqualBitScanLifetime.parentCap,
    GeneralPaperEqualBitScanLifetime.totalWork,
    GeneralPaperEqualBitBoundaryScan.stepBound,
    GeneralPaperEqualBitVertexLifetime.profile,
    GeneralPaperEqualBitVertexLifetime.copyProfile,
    GeneralPaperEqualBitVertexLifetime.callbackPrice,
    GeneralPaperEqualBitVertexLifetime.parentCap,
    GeneralPaperAdditivePayloadFillStorage.profile,
    GeneralPaperEqualFirstSourceSpace.profile,
    GeneralPaperEqualFirstPackingCallerLifetime.profile,
    GeneralPaperEqualFirstRouteCallerLifetime.profile,
    GeneralPaperEqualFirstInitialPrefixLifetime.profile,
    GeneralPaperEqualFirstInitialPrefixLifetime.roundedProfile,
    GeneralPaperEqualFirstInitialPrefixLifetime.inputProfile,
    GeneralPaperEqualFirstInitialPrefixLifetime.roundingTime,
    GeneralPaperEqualFirstSegmentCallerSpace.sourcePriceCap,
    GeneralPaperEqualFirstPrefixRates.prefixBound,
    GeneralPaperEqualFirstPrefixRates.packingBound,
    GeneralPaperEqualFirstPrefixRates.routeBound,
    GeneralPaperEqualFirstPreparationRates.profile,
    GeneralPaperEqualFirstPreparationRates.aggregate,
    GeneralPaperValueRoundingInputPrice.size,
    GeneralPaperValueRoundingPaperContract.scaleBitProfile,
    GeneralPaperNaturalPrimitivePrice.binary,
    GeneralPaperNaturalPrimitivePrice.word,
    GeneralPaperEqualBitBranchRates.scanProfile,
    GeneralPaperEqualBitVertex.bound,
    GeneralPaperEqualSelectedClosureLifetime.profile,
    GeneralPaperEqualSelectedClosureLifetime.componentProfile,
    GeneralPaperEqualSelectedClosureLifetime.controlProfile,
    GeneralPaperEqualSelectedClosureLifetime.controlCap,
    GeneralPaperEqualSelectedBranchOwner.profile,
    GeneralPaperEqualSelectedBranchOwner.pureProfile,
    GeneralPaperEqualSelectedClosureWork.price,
    GeneralPaperEqualSelectedClosureWork.basePrice,
    GeneralPaperEqualDescriptionRates.paperBound,
    GeneralPaperEqualFirstSelectedSpace.profile,
    GeneralPaperEqualFirstSelectedSpace.short,
    GeneralPaperEqualFirstSelectedSpace.parentProfile,
    GeneralPaperEqualFirstSelectedSpace.parentCap,
    GeneralPaperEqualFirstSelectedDescription.closureProfile,
    GeneralPaperEqualFirstSelectedPreparation.bound,
    GeneralPaperEqualFirstPreparationWork.bound,
    GeneralPaperEqualFirstPreparationWork.continuationBound,
    GeneralPaperEqualFirstClosureRates.bound,
    GeneralPaperEqualFirstInputResources.parentCap,
    GeneralPaperEqualFirstInputPipeline.price]
  fun_prop (config := {maxSteps := 100000})

theorem parent_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => GeneralPaperEqualFirstInputResources.parentProfile model (word K p) K p) ledger logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model,1 ≤ ledger p := GeneralPaperEqualInputDomain.ledger_positive
  have hCap := parent_cap_small model hFast id (word K) (fun _ => K) logarithm hL
    (GeneralPaperEqualInputRates.common_word_small model K) (small_constant K logarithm hL)
    (GeneralPaperEqualInputDomain.count_small model) (GeneralPaperEqualInputDomain.exponent_tight model)
    (GeneralPaperEqualInputRates.value_small model) (GeneralPaperEqualInputRates.original_budget_small model)
    (GeneralPaperEqualInputDomain.accuracy_small model)
  dsimp only [GeneralPaperEqualFirstInputResources.parentProfile]
  fun_prop

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => GeneralPaperEqualFirstInputResources.profile model (word K p) K p) ledger logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model,1 ≤ ledger p := GeneralPaperEqualInputDomain.ledger_positive
  have hInit := GeneralPaperMixedInitializerCalibration.profile_rate model hFast K
  have hReturn := dominated (GeneralPaperEqualInputInitializerCapacity.profile_rate model hFast K)
    (fun p => returned_le_profile model (word K p) K p)
  have hSelected := GeneralPaperEqualFirstSelectedRates.profile_rate model hFast K
  have hParent := parent_rate model hFast K
  dsimp only [GeneralPaperEqualFirstInputResources.profile]
  fun_prop

theorem uniform_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ),
      binaryWordWidth (GeneralPaperEqualFirstInputResources.profile model W K p) ≤
        C*(logarithm p+binaryWordWidth W+binaryWordWidth K) := by
  let L := GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure (model := model)
  have hL : ∀ a : GeneralPaperEqualInputInitializerCapacity.Parameters model,1 ≤ L a :=
    GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hS := GeneralPaperEqualInputInitializerCapacity.lift_small model originalSize (GeneralPaperEqualInputDomain.original_small model)
  have hSRaw : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => GeneralPaperValueRoundingInputPrice.inputSize a.input.values) L := hS
  have hb := GeneralPaperEqualInputInitializerCapacity.lift_small model budgetSize (GeneralPaperEqualInputDomain.budget_small model)
  have hbRaw : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => rationalWordWidth a.input.budget) L := hb
  have hE := GeneralPaperEqualInputInitializerCapacity.lift_small model accuracySize (GeneralPaperEqualInputDomain.accuracy_small model)
  have hn := GeneralPaperEqualInputInitializerCapacity.lift_small model (fun p => p.n) (GeneralPaperEqualInputDomain.count_small model)
  have hk := GeneralPaperEqualInputInitializerCapacity.lift_tight model (fun p => p.k) (GeneralPaperEqualInputDomain.exponent_tight model)
  have hW : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => a.reference) L := by
    refine ⟨1,fun a => ?_⟩
    dsimp only [L,GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure]; omega
  have hK : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => a.coefficient) L := by
    refine ⟨1,fun a => ?_⟩
    dsimp only [L,GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure]; omega
  obtain ⟨CI,hI⟩ := GeneralPaperMixedInitializerCalibration.uniform_word_growth model hFast
  have hInit : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperMixedInitializerPhases.profile model a.reference a.coefficient a.input) L :=
    ⟨CI,fun a => hI a.input a.reference a.coefficient⟩
  obtain ⟨CR,hR⟩ := GeneralPaperEqualInputInitializerCapacity.uniform_word_growth model hFast
  have hReturn : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualInputInitializerLifetime.returnedProfile model a.reference a.coefficient a.input) L :=
    small_mono ⟨CR,fun a => hR a.input a.reference a.coefficient⟩
      (fun a => returned_le_profile model a.reference a.coefficient a.input)
  obtain ⟨CS,hS'⟩ := GeneralPaperEqualFirstSelectedRates.uniform_word_growth model hFast
  have hSelected : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualFirstSelectedSpace.profile model a.reference a.input) L :=
    ⟨CS,fun a => hS' a.input a.reference a.coefficient⟩
  have hCap := parent_cap_small model hFast
    (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => a.input) (fun a => a.reference)
    (fun a => a.coefficient) L hL hW hK hn hk hSRaw hbRaw hE
  have hAll : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualFirstInputResources.profile model a.reference a.coefficient a.input) L := by
    dsimp only [GeneralPaperEqualFirstInputResources.profile,GeneralPaperEqualFirstInputResources.parentProfile]
    fun_prop
  obtain ⟨C,hC⟩ := hAll
  exact ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

theorem uniform_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ,1 ≤ K ∧ ∀ p : Input model,
      GeneralPaperEqualFirstInputResources.profile model (word K p) K p < 2^word K p :=
  GeneralPaperSelfReferenceCapacity.uniform_capacity (GeneralPaperEqualFirstInputResources.profile model)
    logarithm logarithm_positive (uniform_word_growth model hFast)

end Blotto.GeneralPaperEqualFirstInputCapacity
