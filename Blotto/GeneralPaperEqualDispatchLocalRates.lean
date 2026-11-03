import Blotto.GeneralPaperEqualBitScanLifetime
import Blotto.GeneralPaperEqualInputInitializerCapacity

/-! Uniform sharp and word-growth bounds for the actual new scan/pure
lifetimes and the branch-independent once-built rounding/length prefix. -/
namespace Blotto.GeneralPaperEqualDispatchLocalRates
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def short {model : RationalCostModel} (p : Input model) : ℕ := 1 + 6 * (binaryWordWidth p.n + p.k + 11)
def scanProfile (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualBitScanLifetime.profile model W p.n (short p)
def vertexProfile {model : RationalCostModel} (W : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualBitVertexLifetime.profile W p.n (rationalWordWidth p.budget)
def prefixProfile (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualInitialPrefixLifetime.profile model W W p.k p.values p.budget
def profile (model : RationalCostModel) (W : ℕ) (p : Input model) : ℕ :=
  prefixProfile model W p + scanProfile model W p + vertexProfile W p

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => profile model (word K p) p) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  dsimp only [profile, scanProfile, vertexProfile, prefixProfile, short,
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
    GeneralPaperPackingAllocationLifetime.indicesProfile,
    GeneralPaperIndexedArrayLifetime.frame,
    GeneralPaperPositiveScanLifetime.labelProfile,
    GeneralPaperEqualRouteConstruction.indicesWork,
    expressionHeightBudget]
  fun_prop (config := {maxSteps := 50000})

theorem uniform_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ),
      binaryWordWidth (profile model W p) ≤ C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  let L := GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure (model := model)
  have hL : ∀ a : GeneralPaperEqualInputInitializerCapacity.Parameters model, 1 ≤ L a :=
    GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hS := GeneralPaperEqualInputInitializerCapacity.lift_small model originalSize (GeneralPaperEqualInputDomain.original_small model)
  have hSRaw : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => GeneralPaperValueRoundingInputPrice.inputSize a.input.values) L := hS
  have hb := GeneralPaperEqualInputInitializerCapacity.lift_small model budgetSize (GeneralPaperEqualInputDomain.budget_small model)
  have hbRaw : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => rationalWordWidth a.input.budget) L := hb
  have hn := GeneralPaperEqualInputInitializerCapacity.lift_small model (fun p => p.n) (GeneralPaperEqualInputDomain.count_small model)
  have hk := GeneralPaperEqualInputInitializerCapacity.lift_tight model (fun p => p.k) (GeneralPaperEqualInputDomain.exponent_tight model)
  have hkSmall := small_of_tight hk hL
  have hW : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => a.reference) L := by
    refine ⟨1, fun a => ?_⟩
    dsimp only [L, GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure]
    omega
  have hAll : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => profile model a.reference a.input) L := by
    dsimp only [profile, scanProfile, vertexProfile, prefixProfile, short,
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
    GeneralPaperPackingAllocationLifetime.indicesProfile,
    GeneralPaperIndexedArrayLifetime.frame,
    GeneralPaperPositiveScanLifetime.labelProfile,
    GeneralPaperEqualRouteConstruction.indicesWork,
    expressionHeightBudget]
    fun_prop (config := {maxSteps := 50000})
  obtain ⟨C, hC⟩ := hAll
  exact ⟨C, fun p W K => hC ⟨p,W,K⟩⟩

end Blotto.GeneralPaperEqualDispatchLocalRates
