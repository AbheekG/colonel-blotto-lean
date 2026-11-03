import Blotto.GeneralPaperEqualPureCopyLifetime

/-! The literal pure-row copy lifetimes are linear in aggregate input size
up to logarithms. The sole large budget encoding occurs additively; its
maximum size enters recursive metadata only through an encoded word length. -/
namespace Blotto.GeneralPaperEqualPureCopyRates
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem profile_rate (model : RationalCostModel) (K : ℕ) :
    Bound (fun p : Input model => GeneralPaperEqualPureCopyLifetime.profile (word K p) p.n p.k
      (rationalWordWidth p.budget)) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  dsimp only [GeneralPaperEqualPureCopyLifetime.profile,GeneralPaperScalarTableCopyLifetime.profile,
    GeneralPaperScalarTableCopyLifetime.scalarProfile,GeneralPaperScalarTableCopyLifetime.scalarPrice,
    GeneralPaperReferenceArrayCopyLifetime.profile,GeneralPaperReferenceArrayCopyLifetime.parentCap,
    GeneralPaperDualWidthFillStorage.profile,GeneralPaperAdditivePayloadFillStorage.profile,
    GeneralPaperNativePayloadFillStorage.frameProfile,GeneralPaperNativePayloadFillStorage.metadataCap,
    GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperEncodedScalarStorage.natBits,
    GeneralPaperEqualBitDrawRates.address,StoredArrayReferenceList.poolAddressWidth,
    GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
  fun_prop (config := {maxSteps := 50000})

theorem uniform_word_growth (model : RationalCostModel) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ),
      binaryWordWidth (GeneralPaperEqualPureCopyLifetime.profile W p.n p.k (rationalWordWidth p.budget)) ≤
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
      GeneralPaperEqualPureCopyLifetime.profile a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L := by
    dsimp only [GeneralPaperEqualPureCopyLifetime.profile,GeneralPaperScalarTableCopyLifetime.profile,
      GeneralPaperScalarTableCopyLifetime.scalarProfile,GeneralPaperScalarTableCopyLifetime.scalarPrice,
      GeneralPaperReferenceArrayCopyLifetime.profile,GeneralPaperReferenceArrayCopyLifetime.parentCap,
      GeneralPaperDualWidthFillStorage.profile,GeneralPaperAdditivePayloadFillStorage.profile,
      GeneralPaperNativePayloadFillStorage.frameProfile,GeneralPaperNativePayloadFillStorage.metadataCap,
      GeneralPaperNativePayloadFillStorage.workCap,GeneralPaperEncodedScalarStorage.natBits,
      GeneralPaperEqualBitDrawRates.address,StoredArrayReferenceList.poolAddressWidth,
      GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
    fun_prop (config := {maxSteps := 50000})
  obtain ⟨C,hC⟩ := hAll
  exact ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

end Blotto.GeneralPaperEqualPureCopyRates
