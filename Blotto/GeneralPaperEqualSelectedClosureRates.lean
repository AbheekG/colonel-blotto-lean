import Blotto.GeneralPaperEqualSelectedClosureLifetime

/-! Sharp original-input rates and uniform word growth of the complete
local closure reserve, including actual branch and returned closure owners. -/
namespace Blotto.GeneralPaperEqualSelectedClosureRates
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => GeneralPaperEqualSelectedClosureLifetime.profile model (word K p)
      p.n p.k (rationalWordWidth p.budget)) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  dsimp only [GeneralPaperEqualSelectedClosureLifetime.profile,
    GeneralPaperEqualSelectedClosureLifetime.componentProfile,GeneralPaperEqualSelectedClosureLifetime.controlProfile,
    GeneralPaperEqualSelectedClosureLifetime.controlCap,GeneralPaperEqualSelectedBranchOwner.profile,
    GeneralPaperEqualSelectedBranchOwner.pureProfile,GeneralPaperEqualNativeRetainedStorage.profile,
    GeneralPaperEqualNativeRetainedStorage.height,GeneralPaperEqualNativeRetainedStorage.short,
    GeneralPaperEqualRetainedStorage.preparedProfile,GeneralPaperEqualRetainedStorage.cacheProfile,
    GeneralPaperEqualRetainedStorage.segmentProfile,GeneralPaperEqualRetainedStorage.wordProfile,
    GeneralPaperEncodedBasisStorage.arrayProfile,GeneralPaperWordLengthLifetime.rationalProfile,
    GeneralPaperAddressConstructionLifetime.profile,GeneralPaperEqualSelectedClosureWork.price,
    GeneralPaperEqualSelectedClosureWork.basePrice,GeneralPaperEqualAddressConstruction.operandWidth,
    GeneralPaperEqualDescriptionRates.paperBound,GeneralPaperEqualBitDrawRates.log,
    GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size,expressionHeightBudget]
  fun_prop (config := {maxSteps := 50000})

theorem uniform_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ),
      binaryWordWidth (GeneralPaperEqualSelectedClosureLifetime.profile model W p.n p.k (rationalWordWidth p.budget)) ≤
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
      GeneralPaperEqualSelectedClosureLifetime.profile model a.reference a.input.n a.input.k (rationalWordWidth a.input.budget)) L := by
    dsimp only [GeneralPaperEqualSelectedClosureLifetime.profile,
      GeneralPaperEqualSelectedClosureLifetime.componentProfile,GeneralPaperEqualSelectedClosureLifetime.controlProfile,
      GeneralPaperEqualSelectedClosureLifetime.controlCap,GeneralPaperEqualSelectedBranchOwner.profile,
      GeneralPaperEqualSelectedBranchOwner.pureProfile,GeneralPaperEqualNativeRetainedStorage.profile,
      GeneralPaperEqualNativeRetainedStorage.height,GeneralPaperEqualNativeRetainedStorage.short,
      GeneralPaperEqualRetainedStorage.preparedProfile,GeneralPaperEqualRetainedStorage.cacheProfile,
      GeneralPaperEqualRetainedStorage.segmentProfile,GeneralPaperEqualRetainedStorage.wordProfile,
      GeneralPaperEncodedBasisStorage.arrayProfile,GeneralPaperWordLengthLifetime.rationalProfile,
      GeneralPaperAddressConstructionLifetime.profile,GeneralPaperEqualSelectedClosureWork.price,
      GeneralPaperEqualSelectedClosureWork.basePrice,GeneralPaperEqualAddressConstruction.operandWidth,
      GeneralPaperEqualDescriptionRates.paperBound,GeneralPaperEqualBitDrawRates.log,
      GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size,expressionHeightBudget]
    fun_prop (config := {maxSteps := 50000})
  obtain ⟨C,hC⟩ := hAll
  exact ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

end Blotto.GeneralPaperEqualSelectedClosureRates
