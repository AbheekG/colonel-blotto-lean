import Blotto.GeneralPaperEqualSelectedCopyLifetime

/-! Sharp original-input rates and uniform word growth for the complete
selected-copy reserve, including both branches, mixed reference widths and
all new outer controls. These copy bounds require no rational-cost growth. -/
namespace Blotto.GeneralPaperEqualSelectedCopyLifetimeRates
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem profile_rate (model : RationalCostModel) (K : ℕ) :
    Bound (fun p : Input model => GeneralPaperEqualSelectedCopyLifetime.profile (word K p) p.n p.k
      (rationalWordWidth p.budget)) ledger logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model,1 ≤ ledger p := ledger_positive
  have hGrouped := GeneralPaperEqualNativeCopyLifetimeRates.profile_rate model K
  have hCopy := GeneralPaperEqualCopyRates.profile_rate model K
  have hLedger : Small (ledger (model := model)) logarithm := below_ledger_small _ (fun _ => le_rfl)
  have hCopySmall := bound_small hL hCopy hLedger
  dsimp only [GeneralPaperEqualSelectedCopyLifetime.profile,
    GeneralPaperEqualSelectedBranchOwner.profile,
    GeneralPaperEqualSelectedBranchOwner.pureProfile,
    GeneralPaperEqualNativeRetainedStorage.profile,
    GeneralPaperEqualNativeRetainedStorage.height,
    GeneralPaperEqualNativeRetainedStorage.short,
    GeneralPaperEqualRetainedStorage.preparedProfile,
    GeneralPaperEqualRetainedStorage.cacheProfile,
    GeneralPaperEqualRetainedStorage.segmentProfile,
    GeneralPaperEqualRetainedStorage.wordProfile,
    GeneralPaperEncodedBasisStorage.arrayProfile,
    GeneralPaperEqualDescriptionRates.paperBound,
    GeneralPaperEqualSelectedCopyComponents.profile,
    GeneralPaperEqualSelectedCopyControls.profile,
    GeneralPaperEqualSelectedCopyControls.parentCap,
    GeneralPaperEqualSelectedCopyControls.cap,
    GeneralPaperScalarTableCopyLifetime.profile,
    GeneralPaperScalarTableCopyLifetime.scalarProfile,
    GeneralPaperScalarTableCopyLifetime.scalarPrice,
    GeneralPaperReferenceArrayCopyLifetime.profile,
    GeneralPaperReferenceArrayCopyLifetime.parentCap,
    GeneralPaperDualWidthFillStorage.profile,
    GeneralPaperAdditivePayloadFillStorage.profile,
    GeneralPaperNativePayloadFillStorage.frameProfile,
    GeneralPaperNativePayloadFillStorage.metadataCap,
    GeneralPaperNativePayloadFillStorage.workCap,
    GeneralPaperEncodedScalarStorage.natBits,
    GeneralPaperEqualBitDrawRates.log,
    GeneralPaperEqualBitDrawRates.word,
    GeneralPaperEqualBitDrawRates.size]
  fun_prop (config := {maxSteps := 100000})

theorem uniform_word_growth (model : RationalCostModel) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ),
      binaryWordWidth (GeneralPaperEqualSelectedCopyLifetime.profile W p.n p.k (rationalWordWidth p.budget)) ≤
        C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨Cg,hg⟩ := GeneralPaperEqualNativeCopyLifetimeRates.uniform_word_growth model
  obtain ⟨Cc,hc⟩ := GeneralPaperEqualCopyRates.uniform_word_growth model
  let L := GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure (model := model)
  have hL : ∀ a : GeneralPaperEqualInputInitializerCapacity.Parameters model,1 ≤ L a :=
    GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hGrouped : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualNativeCopyLifetime.profile a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L :=
    ⟨Cg,fun a => hg a.input a.reference a.coefficient⟩
  have hCopy : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualSelectedCopyWork.profile a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L :=
    ⟨Cc,fun a => hc a.input a.reference a.coefficient⟩
  have hb := GeneralPaperEqualInputInitializerCapacity.lift_small model budgetSize (GeneralPaperEqualInputDomain.budget_small model)
  have hbRaw : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => rationalWordWidth a.input.budget) L := hb
  have hn := GeneralPaperEqualInputInitializerCapacity.lift_small model (fun p => p.n) (GeneralPaperEqualInputDomain.count_small model)
  have hk := GeneralPaperEqualInputInitializerCapacity.lift_tight model (fun p => p.k) (GeneralPaperEqualInputDomain.exponent_tight model)
  have hkSmall := small_of_tight hk hL
  have hW : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => a.reference) L := by
    refine ⟨1,fun a => ?_⟩
    dsimp only [L,GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure]; omega
  have hAll : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualSelectedCopyLifetime.profile a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L := by
    dsimp only [GeneralPaperEqualSelectedCopyLifetime.profile,
      GeneralPaperEqualSelectedBranchOwner.profile,
      GeneralPaperEqualSelectedBranchOwner.pureProfile,
      GeneralPaperEqualNativeRetainedStorage.profile,
      GeneralPaperEqualNativeRetainedStorage.height,
      GeneralPaperEqualNativeRetainedStorage.short,
      GeneralPaperEqualRetainedStorage.preparedProfile,
      GeneralPaperEqualRetainedStorage.cacheProfile,
      GeneralPaperEqualRetainedStorage.segmentProfile,
      GeneralPaperEqualRetainedStorage.wordProfile,
      GeneralPaperEncodedBasisStorage.arrayProfile,
      GeneralPaperEqualDescriptionRates.paperBound,
      GeneralPaperEqualSelectedCopyComponents.profile,
      GeneralPaperEqualSelectedCopyControls.profile,
      GeneralPaperEqualSelectedCopyControls.parentCap,
      GeneralPaperEqualSelectedCopyControls.cap,
      GeneralPaperScalarTableCopyLifetime.profile,
      GeneralPaperScalarTableCopyLifetime.scalarProfile,
      GeneralPaperScalarTableCopyLifetime.scalarPrice,
      GeneralPaperReferenceArrayCopyLifetime.profile,
      GeneralPaperReferenceArrayCopyLifetime.parentCap,
      GeneralPaperDualWidthFillStorage.profile,
      GeneralPaperAdditivePayloadFillStorage.profile,
      GeneralPaperNativePayloadFillStorage.frameProfile,
      GeneralPaperNativePayloadFillStorage.metadataCap,
      GeneralPaperNativePayloadFillStorage.workCap,
      GeneralPaperEncodedScalarStorage.natBits,
      GeneralPaperEqualBitDrawRates.log,
      GeneralPaperEqualBitDrawRates.word,
      GeneralPaperEqualBitDrawRates.size]
    fun_prop (config := {maxSteps := 100000})
  obtain ⟨C,hC⟩ := hAll
  exact ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

end Blotto.GeneralPaperEqualSelectedCopyLifetimeRates
