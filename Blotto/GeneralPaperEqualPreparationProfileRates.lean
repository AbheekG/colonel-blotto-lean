import Blotto.GeneralPaperEqualBitPreparationRates

/-! Sharp growth of the complete native preparation reserve. The two word
parameters are still explicit logarithmically bounded analysis families;
this does not compute a common reference or prove a representation join. -/
namespace Blotto.GeneralPaperEqualPreparationProfileRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth
open GeneralPaperEqualRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (W A n m c width : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ) (budget : Input → ℚ)
    (hW : Tight W) (hA : Tight A) (hn : Small n) (hm : Polylog m) (hc : Polylog c) (hWidth : Polylog width)
    (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)))
    (hb : Small (fun x => rationalWordWidth (budget x)))
    (hD : Small (fun x => GeneralPaperEqualNativeSampler.roundDen true model (W x) x.k (values x))) :
    Linear (fun x => GeneralPaperEqualPreparationLifetime.profile model (W x) (A x) x.k
      (m x) (c x) (width x) (values x) (budget x))
      (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x) + rationalWordWidth (budget x) + n x) := by
  let S := fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)
  let b := fun x => rationalWordWidth (budget x)
  let r := fun x => S x + b x + n x
  have hnRate : Linear n r := bounded 1 (fun x => by dsimp [r]; omega)
  have hSRate : Linear S r := bounded 1 (fun x => by dsimp [r]; omega)
  have hbRate : Linear b r := bounded 1 (fun x => by dsimp [r]; omega)
  have hrSmall : Small r := by dsimp [r]; fun_prop
  have hw := of_tight hW
  have ha := of_tight hA
  have hmSmall := poly_small hm
  have hcSmall := poly_small hc
  have hWidthSmall := poly_small hWidth
  have hWPoly : Polylog W := poly_tight W hW
  have hAPoly : Polylog A := poly_tight A hA
  have hKPoly : Polylog Input.k := poly_tight Input.k k_tight
  have hWRate : Linear W r := linear_poly W r hWPoly
  have hARate : Linear A r := linear_poly A r hAPoly
  have hKRate : Linear Input.k r := linear_poly Input.k r hKPoly
  have hmRate : Linear m r := linear_poly m r hm
  have hcRate : Linear c r := linear_poly c r hc
  have hWidthRate : Linear width r := linear_poly width r hWidth
  have hPowerSmall : Small (fun x => 2 ^ (x.k + 5)) := pow_two _ (by fun_prop)
  have hLedger := GeneralPaperEqualBitPreparationRates.ledger_rate model hFast W A n values budget hW hA hn hS hb
  change Linear _ r at hLedger
  have hLedgerSmall := linear_small hLedger hrSmall
  obtain ⟨C, d, hg⟩ := hFast
  have hFast : GeneralPaperFastRationalModel.IsFast model := ⟨C, d, hg⟩
  have hRound := GeneralPaperNativeScaleConstructionStorage.rounding_profile_rate hg W (fun _ => 128) n S
    hW (small_constant 128) hn hS
  have hRoundRate : Linear (fun x => GeneralPaperNativeScaleConstructionStorage.roundingProfile model
      (W x) 128 (n x) x.k (S x)) r := rate_mono hRound (fun x => by dsimp [r]; omega)
  have hRoundTimeSmall : Small (fun x => GeneralPaperNativeScaleConstructionStorage.roundingPrice model
      (W x) 128 (n x) x.k (S x)) := by
    unfold GeneralPaperNativeScaleConstructionStorage.roundingPrice GeneralPaperNativeScaleConstructionStorage.price
      GeneralPaperOriginalSourceValuePrice.scalePrice GeneralPaperOriginalSourceValuePrice.scaleWidth
      GeneralPaperValueWeightSumConstructionStorage.driverPrice GeneralPaperValueWeightSumConstructionStorage.price
      GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice
      GeneralPaperNativePayloadFillStorage.workCap GeneralPaperValueRoundingPaperContract.scale
      GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth GeneralPaperSummaryArrayExecution.arrayWord
      GeneralPaperNatPowerOperands.width
    dsimp only
    fun_prop (config := {maxSteps := 20000})
  dsimp only [S, b] at hSRate hbRate hRoundRate hRoundTimeSmall
  change Linear _ r
  dsimp only [GeneralPaperEqualPreparationLifetime.profile,
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
    expressionHeightBudget]
  fun_prop (config := {maxSteps := 50000})


theorem denominator_small (model : RationalCostModel) (W n : Input → ℕ)
    (values : (x : Input) → FixedArrayTable (n x) ℚ) (v : (x : Input) → RationalFieldSelector (n x))
    (hv : ∀ x j, (values x).read j = (v x).weight j) (hn : Small n) :
    Small (fun x => GeneralPaperEqualNativeSampler.roundDen true model (W x) x.k (values x)) := by
  have hShort : Tight (fun x => binaryWordWidth (n x) + x.k + 9) := by fun_prop
  obtain ⟨C, hC⟩ := hShort
  exact ⟨C, fun x => (GeneralPaperEqualNativeSampler.roundDen_word true model (W x) x.k
    (values x) (v x) (hv x)).trans (hC x)⟩

theorem native_profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (W A n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x))
    (hv : ∀ x j, (values x).read j = (v x).weight j)
    (small : ∀ x j, 2 * (GeneralPaperEqualNativeSampler.rounded true model (W x) x.k (values x) (v x) (hv x)).weight j ≤ 1)
    (budget : Input → ℚ) (hW : Tight W) (hA : Tight A) (hn : Small n)
    (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)))
    (hb : Small (fun x => rationalWordWidth (budget x))) :
    Linear (fun x =>
      let r := GeneralPaperEqualNativeSampler.rounded true model (W x) x.k (values x) (v x) (hv x)
      GeneralPaperEqualPreparationLifetime.profile model (W x) (A x) x.k
        (GeneralPaperEqualFiniteKernel.terminal r (small x)).groups.length
        (GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery r (small x)))
        (GeneralPaperEqualNativeCache.prepare true model (W x) x.k (values x) (v x) (hv x) (small x) (budget x)).rangeBits
        (values x) (budget x))
      (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x) + rationalWordWidth (budget x) + n x) := by
  let r := fun x => GeneralPaperEqualNativeSampler.rounded true model (W x) x.k (values x) (v x) (hv x)
  let m := fun x => (GeneralPaperEqualFiniteKernel.terminal (r x) (small x)).groups.length
  let c := fun x => GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery (r x) (small x))
  let width := fun x => (GeneralPaperEqualNativeCache.prepare true model (W x) x.k
    (values x) (v x) (hv x) (small x) (budget x)).rangeBits
  have hm : Polylog m := GeneralPaperSourceSoftBounds.dominated (poly_constant 3)
    (fun x => GeneralPaperEqualNativeCache.group_count (r x) (small x))
  have hc : Polylog c := GeneralPaperSourceSoftBounds.dominated (poly_constant 7)
    (fun x => (GeneralPaperEqualNativeCache.compact_count (r x) (small x)).2)
  have hWidthCap : Polylog (fun x => 3670016 * (binaryWordWidth (n x) + x.k + 10) + 1) := by
    have hK : Polylog Input.k := poly_tight _ k_tight
    fun_prop
  have hWidth : Polylog width := GeneralPaperSourceSoftBounds.dominated hWidthCap
    (fun x => GeneralPaperEqualNativeCache.rangeBits true model (W x) x.k
      (values x) (v x) (hv x) (small x) (budget x))
  exact profile_rate model hFast W A n m c width values budget hW hA hn hm hc hWidth hS hb
    (denominator_small model W n values v hv hn)

/-- Uniformly bounds any selection of reached phases, including the returned
sampler/work record and arrays built at the original reference width. -/
theorem all_phase_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (W A n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x))
    (hv : ∀ x j, (values x).read j = (v x).weight j)
    (small : ∀ x j, 2 * (GeneralPaperEqualNativeSampler.rounded true model (W x) x.k (values x) (v x) (hv x)).weight j ≤ 1)
    (budget : Input → ℚ) (hW : Tight W) (hA : Tight A) (hn : Small n)
    (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)))
    (hb : Small (fun x => rationalWordWidth (budget x)))
    (phase : (x : Input) → GeneralPaperEqualPreparationLifetime.Phase (n x)
      (GeneralPaperEqualFiniteKernel.terminal (GeneralPaperEqualNativeSampler.rounded true model (W x) x.k
        (values x) (v x) (hv x)) (small x)).groups.length
      (GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery
        (GeneralPaperEqualNativeSampler.rounded true model (W x) x.k (values x) (v x) (hv x)) (small x)))
      (x.k + 5) (GeneralPaperEqualNativeCache.prepare true model (W x) x.k
        (values x) (v x) (hv x) (small x) (budget x)).rangeBits) :
    Linear (fun x => GeneralPaperEqualPreparationLifetime.window model (W x) (A x) x.k
      (values x) (v x) (hv x) (small x) (budget x) (phase x))
      (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x) + rationalWordWidth (budget x) + n x) :=
  GeneralPaperSourceSoftBounds.dominated
    (native_profile_rate model hFast W A n values v hv small budget hW hA hn hS hb)
    (fun x => GeneralPaperEqualPreparationLifetime.all_phases model (W x) (A x) x.k
      (values x) (v x) (hv x) (small x) (budget x) (phase x))

end Blotto.GeneralPaperEqualPreparationProfileRates
