import Blotto.GeneralPaperEqualReferenceConstruction

/-! One uniform logarithmic word covers the complete grouped-equal native
preparation reserve. It is a fixed multiple of input-length/precision data;
no storage/cost profile is evaluated by the proposed word constructor.
Pricing the measured-input-length constructor and joining the returned draw
representation remain explicit later obligations. -/
namespace Blotto.GeneralPaperEqualCommonReference
open GeneralPaperEqualResourceDomain GeneralPaperUniformResourceGrowth
open GeneralPaperUniformLinearReference
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def reserve (model : RationalCostModel) (W : ℕ) (p : Problem model) : ℕ :=
  GeneralPaperBinaryAccuracyConstructionStorage.profile W (accuracySize p) +
    GeneralPaperEqualPreparationLifetime.profile model W W p.k (groups p) (segments p) (width p) p.values p.budget


theorem dimensions_congr {n : ℕ} (r s : RationalFieldSelector n) (h : r = s)
    (hr : ∀ j, 2 * r.weight j ≤ 1) (hs : ∀ j, 2 * s.weight j ≤ 1) (k : ℕ) (budget : ℚ) :
    (GeneralPaperEqualFiniteKernel.terminal r hr).groups.length = (GeneralPaperEqualFiniteKernel.terminal s hs).groups.length ∧
    GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery r hr) =
      GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery s hs) ∧
    (GeneralPaperEqualPreparedCache.prepare (GeneralPaperEqualFiniteKernel.terminal r hr).partition
      (GeneralPaperEqualFiniteKernel.lottery r hr) k budget).rangeBits =
    (GeneralPaperEqualPreparedCache.prepare (GeneralPaperEqualFiniteKernel.terminal s hs).partition
      (GeneralPaperEqualFiniteKernel.lottery s hs) k budget).rangeBits := by
  subst s
  exact ⟨rfl, rfl, rfl⟩

theorem native_dimensions (model : RationalCostModel) (W : ℕ) (p : Problem model) :
    (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded true model W p.k p.values p.selector p.correct)
      (small_at_reference p W)).groups.length = groups p ∧
    GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery
      (GeneralPaperEqualNativeSampler.rounded true model W p.k p.values p.selector p.correct)
      (small_at_reference p W)) = segments p ∧
    (GeneralPaperEqualNativeCache.prepare true model W p.k p.values p.selector p.correct
      (small_at_reference p W) p.budget).rangeBits = width p := by
  simpa only [groups, segments, width, rounded, GeneralPaperEqualNativeCache.prepare] using
    dimensions_congr _ _ (rounded_reference model W p.k p.values p.selector p.correct)
      (small_at_reference p W) p.small (p.k + 5) p.budget

theorem reserve_scaling (model : RationalCostModel) (p : Problem model) :
    GeneralPaperReferenceScaling.Scale (fun W => reserve model W p) := by
  unfold reserve
  dsimp only [GeneralPaperBinaryAccuracyConstructionStorage.profile,
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
  simp only [denominator_reference model _ _ p.values p.selector p.correct]
  fun_prop (config := {maxSteps := 50000})

theorem reserve_at_one_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (reserve model 1) logarithm := by
  have hL : ∀ p : Problem model, 1 ≤ logarithm p := logarithm_positive
  have hS : Small (fun p : Problem model => GeneralPaperValueRoundingInputPrice.inputSize p.values) logarithm :=
    GeneralPaperEqualResourceDomain.original_small model
  have hb : Small (fun p : Problem model => rationalWordWidth p.budget) logarithm :=
    GeneralPaperEqualResourceDomain.budget_small model
  have hn := count_small model
  have hk := small_of_tight (exponent_tight model) hL
  have hK := exponent_tight model
  have hm := groups_small model
  have hc := segments_small model
  have hw := width_small model
  have hD := denominator_small model
  have hE := accuracy_small model
  unfold reserve
  dsimp only [GeneralPaperBinaryAccuracyConstructionStorage.profile,
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

def word (K : ℕ) {model : RationalCostModel} (p : Problem model) : ℕ := K * logarithm p

theorem uniform_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : Problem model, reserve model (word K p) p < 2 ^ word K p :=
  GeneralPaperUniformLinearReference.uniform_capacity (reserve model) logarithm
    (reserve_scaling model) (reserve_at_one_small model hFast)

theorem word_positive (K : ℕ) (hK : 1 ≤ K) {model : RationalCostModel} (p : Problem model) : 1 ≤ word K p := by
  have h := Nat.mul_le_mul hK (logarithm_positive p)
  simpa only [Nat.one_mul, word] using h

theorem word_tight (K : ℕ) (model : RationalCostModel) : Tight (word K (model := model)) logarithm :=
  ⟨K, fun _ => le_rfl⟩



theorem profile_congr {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) {m c width m' c' width' : ℕ}
    (hm : m = m') (hc : c = c') (hw : width = width') :
    GeneralPaperEqualPreparationLifetime.profile model W A k m c width values budget =
      GeneralPaperEqualPreparationLifetime.profile model W A k m' c' width' values budget := by
  subst m'
  subst c'
  subst width'
  rfl

abbrev Phase (model : RationalCostModel) (W : ℕ) (p : Problem model) :=
  GeneralPaperEqualPreparationLifetime.Phase p.n
    (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded true model W p.k p.values p.selector p.correct)
      (small_at_reference p W)).groups.length
    (GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery
      (GeneralPaperEqualNativeSampler.rounded true model W p.k p.values p.selector p.correct)
      (small_at_reference p W))) (p.k + 5)
    (GeneralPaperEqualNativeCache.prepare true model W p.k p.values p.selector p.correct
      (small_at_reference p W) p.budget).rangeBits

def window (model : RationalCostModel) (W : ℕ) (p : Problem model) (phase : Phase model W p) : ℕ :=
  GeneralPaperBinaryAccuracyConstructionStorage.profile W (accuracySize p) +
    GeneralPaperEqualPreparationLifetime.window model W W p.k p.values p.selector p.correct
      (small_at_reference p W) p.budget phase

theorem native_window_bound (model : RationalCostModel) (W : ℕ) (p : Problem model) (phase : Phase model W p) :
    window model W p phase ≤ reserve model W p := by
  have h := GeneralPaperEqualPreparationLifetime.all_phases model W W p.k p.values p.selector p.correct
    (small_at_reference p W) p.budget phase
  obtain ⟨hm, hc, hw⟩ := native_dimensions model W p
  have hProfile : GeneralPaperEqualPreparationLifetime.profile model W W p.k
      (GeneralPaperEqualFiniteKernel.terminal
        (GeneralPaperEqualNativeSampler.rounded true model W p.k p.values p.selector p.correct)
        (small_at_reference p W)).groups.length
      (GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery
        (GeneralPaperEqualNativeSampler.rounded true model W p.k p.values p.selector p.correct)
        (small_at_reference p W)))
      (GeneralPaperEqualNativeCache.prepare true model W p.k p.values p.selector p.correct
        (small_at_reference p W) p.budget).rangeBits p.values p.budget =
      GeneralPaperEqualPreparationLifetime.profile model W W p.k (groups p) (segments p) (width p) p.values p.budget := by
    exact @profile_congr p.n model W W p.k p.values p.budget _ _ _ _ _ _ hm hc hw
  exact Nat.add_le_add_left (h.trans_eq hProfile) _

theorem measured_word_eq (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    (GeneralPaperEqualReferenceConstruction.measured model A K p.k p.values p.budget p.words).1 = word K p := by
  simp only [GeneralPaperEqualReferenceConstruction.measured_data, word, logarithm, ledger, originalSize,
    budgetSize, accuracySize, GeneralPaperEqualReferenceConstruction.log]

def prepareReference (model : RationalCostModel) (A K : ℕ) (p : Problem model) : (ℕ × ℕ) × ℕ :=
  let precision := GeneralPaperBinaryAccuracy.prepare id A p.words
  let reference := GeneralPaperEqualReferenceConstruction.measured model A K precision.1 p.values p.budget p.words
  ((precision.1, reference.1), precision.2 + reference.2 + 64 * A + 64)

theorem initialized_exponent (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    (prepareReference model A K p).1.1 = p.k := by
  change (GeneralPaperBinaryAccuracy.prepare id A p.words).1 = p.k
  rw [GeneralPaperBinaryAccuracy.prepare_data]
  have h := p.exponent_correct
  rw [GeneralPaperBinaryAccuracy.prepare_data] at h
  exact h.symm

theorem initialized_word (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    (prepareReference model A K p).1.2 = word K p := by
  have h := initialized_exponent model A K p
  change (GeneralPaperBinaryAccuracy.prepare id A p.words).1 = p.k at h
  change (GeneralPaperEqualReferenceConstruction.measured model A K
    (GeneralPaperBinaryAccuracy.prepare id A p.words).1 p.values p.budget p.words).1 = _
  rw [h]
  exact measured_word_eq model A K p

theorem actual_uniform_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (A : ℕ) (p : Problem model),
      let W := (prepareReference model A K p).1.2
      ∀ phase : Phase model W p, window model W p phase < 2 ^ W := by
  obtain ⟨K, hK, hSafe⟩ := uniform_capacity model hFast
  refine ⟨K, hK, fun A p phase => ?_⟩
  have hW := initialized_word model A K p
  exact (native_window_bound model _ p phase).trans_lt (by rw [hW]; exact hSafe p)

def initializationPrice (model : RationalCostModel) (A K : ℕ) (p : Problem model) : ℕ :=
  GeneralPaperBinaryAccuracyConstructionStorage.price A (accuracySize p) +
    GeneralPaperEqualReferenceConstruction.measuredProfile model A K p.n p.k (originalSize p) (budgetSize p)
      (accuracySize p) + 64 * A + 64

theorem initialization_work (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    (prepareReference model A K p).2 ≤ initializationPrice model A K p := by
  have hPrecision := GeneralPaperBinaryAccuracyConstructionStorage.work A p.words
  have hMeasured := GeneralPaperEqualReferenceConstruction.measured_work model A K p.k p.values p.budget p.words
  have hK := initialized_exponent model A K p
  change (GeneralPaperBinaryAccuracy.prepare id A p.words).1 = p.k at hK
  unfold prepareReference
  change (GeneralPaperBinaryAccuracy.prepare id A p.words).2 +
    (GeneralPaperEqualReferenceConstruction.measured model A K
      (GeneralPaperBinaryAccuracy.prepare id A p.words).1 p.values p.budget p.words).2 + 64 * A + 64 ≤ _
  rw [hK]
  change (GeneralPaperBinaryAccuracy.prepare id A p.words).2 ≤
    GeneralPaperBinaryAccuracyConstructionStorage.price A (accuracySize p) at hPrecision
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hPrecision hMeasured) _) _

end Blotto.GeneralPaperEqualCommonReference
