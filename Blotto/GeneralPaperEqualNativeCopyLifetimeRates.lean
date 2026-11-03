import Blotto.GeneralPaperEqualNativeCopyLifetime

/-! Sharp original-input rates, uniform encoded-word growth and one fixed
common reference coefficient for the complete native grouped-copy reserve.
No cost/storage-profile evaluation is inserted into execution. -/
namespace Blotto.GeneralPaperEqualNativeCopyLifetimeRates
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

theorem profile_rate (model : RationalCostModel) (K : ℕ) :
    Bound (fun p : Input model => GeneralPaperEqualNativeCopyLifetime.profile (word K p) p.n p.k
      (rationalWordWidth p.budget)) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  dsimp only [GeneralPaperEqualNativeCopyLifetime.profile,
    GeneralPaperEqualSamplerCopyLifetime.profile,
    GeneralPaperEqualSamplerCopyLifetime.ownerProfile,
    GeneralPaperEqualSamplerCopyLifetime.parentCap,
    GeneralPaperEqualPreparedCopyLifetime.profile,
    GeneralPaperEqualPreparedCopyLifetime.parentCap,
    GeneralPaperEqualRouteCopyLifetime.profile,
    GeneralPaperEqualRouteCopyLifetime.parentCap,
    GeneralPaperEqualRouteCopyLifetime.payload,
    GeneralPaperEqualSegmentCopyLifetime.profile,
    GeneralPaperEqualSegmentCopyLifetime.parentCap,
    GeneralPaperEqualBooleanCopyLifetime.profile,
    GeneralPaperEqualBooleanCopyLifetime.parentCap,
    GeneralPaperEqualBooleanCopyLifetime.rowPayload,
    GeneralPaperEqualBooleanRowCopyLifetime.profile,
    GeneralPaperEqualBooleanRowCopyLifetime.parentCap,
    GeneralPaperEqualBooleanRowCopyLifetime.price,
    GeneralPaperEqualBooleanWordCopyLifetime.profile,
    GeneralPaperEqualBooleanWordCopyLifetime.parentCap,
    GeneralPaperEqualBooleanWordCopyLifetime.bitPrice,
    GeneralPaperMatrixCopyLifetime.profile,
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
    GeneralPaperReferenceListCopyLifetime.profile,
    GeneralPaperReferenceListCopyLifetime.frameProfile,
    GeneralPaperReferenceListCopyLifetime.metadataCap,
    GeneralPaperReferenceListCopyLifetime.workCap,
    GeneralPaperEqualRetainedStorage.preparedProfile,
    GeneralPaperEqualRetainedStorage.cacheProfile,
    GeneralPaperEqualRetainedStorage.segmentProfile,
    GeneralPaperEqualRetainedStorage.wordProfile,
    GeneralPaperEncodedBasisStorage.arrayProfile,
    GeneralPaperEqualSamplerCopy.price,
    GeneralPaperEqualPreparedCopy.price,
    GeneralPaperEqualRationalCopy.routesPrice,
    GeneralPaperEqualRationalCopy.segmentsPrice,
    GeneralPaperScalarTableCopy.matrixPrice,
    GeneralPaperScalarTableCopy.price,
    GeneralPaperReferenceCopy.arrayPrice,
    GeneralPaperEqualBooleanCopy.price,
    GeneralPaperEqualBooleanCopy.wordPrice,
    GeneralPaperEncodedScalarStorage.natBits,
    GeneralPaperEqualNativeRetainedStorage.height,
    GeneralPaperEqualNativeRetainedStorage.short,
    GeneralPaperEqualBitDrawRates.log,
    GeneralPaperEqualBitDrawRates.word,
    GeneralPaperEqualBitDrawRates.size]
  fun_prop (config := {maxSteps := 100000})

theorem uniform_word_growth (model : RationalCostModel) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ),
      binaryWordWidth (GeneralPaperEqualNativeCopyLifetime.profile W p.n p.k (rationalWordWidth p.budget)) ≤
        C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  let L := GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure (model := model)
  have hL : ∀ a : GeneralPaperEqualInputInitializerCapacity.Parameters model, 1 ≤ L a :=
    GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hb := GeneralPaperEqualInputInitializerCapacity.lift_small model budgetSize (GeneralPaperEqualInputDomain.budget_small model)
  have hbRaw : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => rationalWordWidth a.input.budget) L := hb
  have hn := GeneralPaperEqualInputInitializerCapacity.lift_small model (fun p => p.n) (GeneralPaperEqualInputDomain.count_small model)
  have hk := GeneralPaperEqualInputInitializerCapacity.lift_tight model (fun p => p.k) (GeneralPaperEqualInputDomain.exponent_tight model)
  have hkSmall := small_of_tight hk hL
  have hW : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => a.reference) L := by
    refine ⟨1,fun a => ?_⟩
    dsimp only [L,GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure]; omega
  have hAll : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualNativeCopyLifetime.profile a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L := by
    dsimp only [GeneralPaperEqualNativeCopyLifetime.profile,
      GeneralPaperEqualSamplerCopyLifetime.profile,
      GeneralPaperEqualSamplerCopyLifetime.ownerProfile,
      GeneralPaperEqualSamplerCopyLifetime.parentCap,
      GeneralPaperEqualPreparedCopyLifetime.profile,
      GeneralPaperEqualPreparedCopyLifetime.parentCap,
      GeneralPaperEqualRouteCopyLifetime.profile,
      GeneralPaperEqualRouteCopyLifetime.parentCap,
      GeneralPaperEqualRouteCopyLifetime.payload,
      GeneralPaperEqualSegmentCopyLifetime.profile,
      GeneralPaperEqualSegmentCopyLifetime.parentCap,
      GeneralPaperEqualBooleanCopyLifetime.profile,
      GeneralPaperEqualBooleanCopyLifetime.parentCap,
      GeneralPaperEqualBooleanCopyLifetime.rowPayload,
      GeneralPaperEqualBooleanRowCopyLifetime.profile,
      GeneralPaperEqualBooleanRowCopyLifetime.parentCap,
      GeneralPaperEqualBooleanRowCopyLifetime.price,
      GeneralPaperEqualBooleanWordCopyLifetime.profile,
      GeneralPaperEqualBooleanWordCopyLifetime.parentCap,
      GeneralPaperEqualBooleanWordCopyLifetime.bitPrice,
      GeneralPaperMatrixCopyLifetime.profile,
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
      GeneralPaperReferenceListCopyLifetime.profile,
      GeneralPaperReferenceListCopyLifetime.frameProfile,
      GeneralPaperReferenceListCopyLifetime.metadataCap,
      GeneralPaperReferenceListCopyLifetime.workCap,
      GeneralPaperEqualRetainedStorage.preparedProfile,
      GeneralPaperEqualRetainedStorage.cacheProfile,
      GeneralPaperEqualRetainedStorage.segmentProfile,
      GeneralPaperEqualRetainedStorage.wordProfile,
      GeneralPaperEncodedBasisStorage.arrayProfile,
      GeneralPaperEqualSamplerCopy.price,
      GeneralPaperEqualPreparedCopy.price,
      GeneralPaperEqualRationalCopy.routesPrice,
      GeneralPaperEqualRationalCopy.segmentsPrice,
      GeneralPaperScalarTableCopy.matrixPrice,
      GeneralPaperScalarTableCopy.price,
      GeneralPaperReferenceCopy.arrayPrice,
      GeneralPaperEqualBooleanCopy.price,
      GeneralPaperEqualBooleanCopy.wordPrice,
      GeneralPaperEncodedScalarStorage.natBits,
      GeneralPaperEqualNativeRetainedStorage.height,
      GeneralPaperEqualNativeRetainedStorage.short,
      GeneralPaperEqualBitDrawRates.log,
      GeneralPaperEqualBitDrawRates.word,
      GeneralPaperEqualBitDrawRates.size]
    fun_prop (config := {maxSteps := 100000})
  obtain ⟨C,hC⟩ := hAll
  exact ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

theorem uniform_capacity (model : RationalCostModel) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : Input model,
      GeneralPaperEqualNativeCopyLifetime.profile (word K p) p.n p.k (rationalWordWidth p.budget) < 2 ^ word K p :=
  GeneralPaperSelfReferenceCapacity.uniform_capacity
    (fun (W _ : ℕ) (p : Input model) => GeneralPaperEqualNativeCopyLifetime.profile W p.n p.k (rationalWordWidth p.budget))
    logarithm logarithm_positive (uniform_word_growth model)

end Blotto.GeneralPaperEqualNativeCopyLifetimeRates
