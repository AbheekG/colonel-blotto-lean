import Blotto.GeneralPaperFirstStoredResources

/-! Complete direct-installation phase capacity at one globally fixed,
actually computed coefficient. All full prices, resident RAM and enclosing
controls enter the uniform word-growth envelope. -/
namespace Blotto.GeneralPaperFirstStoredCapacity
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
open GeneralPaperEqualInputInitializerCapacity (Parameters logarithmicMeasure)
open GeneralPaperUniformPreparationParameters (S)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

noncomputable def envelope (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperFirstStoredResources.profile model K p+GeneralPaperFirstStoredCaller.cap model K p+
    GeneralPaperFirstStoredWork.price model K p+1

theorem envelope_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => envelope model a.coefficient a.input) logarithmicMeasure := by
  have hL : ∀ a : Parameters model,1 ≤ logarithmicMeasure a := GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hS := GeneralPaperUniformPreparationParameters.word_small model
  have hWord : Small (fun a : Parameters model => word a.coefficient a.input) logarithmicMeasure := hS
  have hK := GeneralPaperUniformPreparationParameters.coefficient_small model
  have hn := GeneralPaperEqualInputInitializerCapacity.lift_small model (fun p => p.n) (count_small model)
  have hk := GeneralPaperEqualInputInitializerCapacity.lift_tight model (fun p => p.k) (exponent_tight model)
  have hkSmall := small_of_tight hk hL
  have hb : Small (fun a : Parameters model => rationalWordWidth a.input.budget) logarithmicMeasure :=
    GeneralPaperEqualInputInitializerCapacity.lift_small model budgetSize (budget_small model)
  have hOriginal : Small (fun a : Parameters model => GeneralPaperValueRoundingInputPrice.inputSize a.input.values) logarithmicMeasure :=
    GeneralPaperEqualInputInitializerCapacity.lift_small model originalSize (original_small model)
  have hAccuracy := GeneralPaperEqualInputInitializerCapacity.lift_small model accuracySize (accuracy_small model)
  have hAddressTight := GeneralPaperFirstStoredFamilies.address_tight model
    (fun a : Parameters model => a.input) S logarithmicMeasure (GeneralPaperFirstStoredFamilies.source model) hL hn hk hb
  have hAddress : Small (fun a : Parameters model =>
      (GeneralPaperFirstStoredCaller.source model a.coefficient a.input).1.address) logarithmicMeasure :=
    small_of_tight hAddressTight hL
  have hParent := GeneralPaperEqualFirstInputCapacity.parent_cap_small model hFast
    (fun a : Parameters model => a.input) S (fun a => a.coefficient) logarithmicMeasure
    hL hS hK hn hk hOriginal hb hAccuracy
  have hInitialPrice : Small (fun a : Parameters model =>
      GeneralPaperEqualFirstInputPipeline.price model (word a.coefficient a.input) a.coefficient a.input) logarithmicMeasure := by
    apply small_mono hParent
    intro a
    dsimp only [GeneralPaperEqualFirstInputResources.parentCap,S]
    omega
  have hConstruct : Small (fun a : Parameters model => GeneralPaperCompleteSelectedPreparationWork.bound model
      (word a.coefficient a.input) (GeneralPaperFirstStoredCaller.source model a.coefficient a.input).1) logarithmicMeasure :=
    (GeneralPaperFirstStoredFamilies.uniform_components model hFast).1
  have hComponents : Small (fun a : Parameters model => GeneralPaperSelectedOuterInputLifetime.combinedBound model
      (word a.coefficient a.input) (GeneralPaperFirstStoredCaller.source model a.coefficient a.input).1) logarithmicMeasure :=
    (GeneralPaperFirstStoredFamilies.uniform_components model hFast).2
  have hPriceMajor : Small (fun a : Parameters model =>
      GeneralPaperEqualFirstInputPipeline.price model (word a.coefficient a.input) a.coefficient a.input+
      GeneralPaperCompleteSelectedPreparationWork.bound model (word a.coefficient a.input)
        (GeneralPaperFirstStoredCaller.source model a.coefficient a.input).1+
      64*(word a.coefficient a.input+(GeneralPaperFirstStoredCaller.source model a.coefficient a.input).1.address+1)) logarithmicMeasure := by
    fun_prop
  have hPrice : Small (fun a : Parameters model => GeneralPaperFirstStoredWork.price model a.coefficient a.input) logarithmicMeasure :=
    small_mono hPriceMajor (fun a => (GeneralPaperFirstStoredWork.price_actual_source model a.coefficient a.input).le)
  have hCap : Small (fun a : Parameters model => GeneralPaperFirstStoredCaller.cap model a.coefficient a.input) logarithmicMeasure := by
    dsimp only [GeneralPaperFirstStoredCaller.cap]
    fun_prop
  have hSource := GeneralPaperUniformPreparationParameters.lift_uniform model
    (GeneralPaperEqualFirstInputResources.profile model) (GeneralPaperEqualFirstInputCapacity.uniform_word_growth model hFast)
  have hSourceOwners : Small (fun a : Parameters model => GeneralPaperFirstStoredCaller.sourceProfile model a.coefficient a.input) logarithmicMeasure := by
    dsimp only [GeneralPaperFirstStoredCaller.sourceProfile,GeneralPaperEqualBitDrawRates.log,
      GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
    fun_prop (config := {maxSteps := 50000})
  have hControls : Small (fun a : Parameters model => GeneralPaperFirstStoredCaller.controlProfile model a.coefficient a.input) logarithmicMeasure := by
    dsimp only [GeneralPaperFirstStoredCaller.controlProfile]
    fun_prop
  have hResult : Small (fun a : Parameters model => GeneralPaperFirstStoredCaller.resultProfile model a.coefficient a.input) logarithmicMeasure := by
    dsimp only [GeneralPaperFirstStoredCaller.resultProfile,GeneralPaperMeasuredPlanLifetimeAlgebra.unit,
      GeneralPaperPayloadInstallationLifetime.cap]
    fun_prop
  have hDescriptionMajor : Small (fun a : Parameters model => 2*GeneralPaperEqualDescriptionRates.paperBound
      a.input.n (a.input.k+1) (rationalWordWidth a.input.budget)) logarithmicMeasure := by
    dsimp only [GeneralPaperEqualDescriptionRates.paperBound,GeneralPaperEqualNativeRetainedStorage.short,
      GeneralPaperEqualBitDrawRates.log,GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
    fun_prop (config := {maxSteps := 50000})
  have hDescription : Small (fun a : Parameters model => GeneralPaperEqualSelectedDescription.footprint
      (GeneralPaperFirstStoredCaller.source model a.coefficient a.input).1) logarithmicMeasure :=
    small_mono hDescriptionMajor (fun a => GeneralPaperEqualFirstSelectedDescription.paper_bound model (S a) a.input.k
      a.input.values a.input.selector a.input.correct a.input.budget _)
  dsimp only [envelope,GeneralPaperFirstStoredResources.profile,GeneralPaperFirstStoredResources.temporaryProfile,
    GeneralPaperFirstStoredCaller.profile]
  fun_prop

theorem uniform_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ,1 ≤ K ∧ ∀ p : Input model,envelope model K p < 2^word K p := by
  obtain ⟨C,hC⟩ := envelope_small model hFast
  exact GeneralPaperSelfReferenceCapacity.uniform_capacity (fun _W K p => envelope model K p)
    logarithm logarithm_positive ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

theorem all_phase_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ,1 ≤ K ∧ ∀ (p : Input model) (phase : GeneralPaperFirstStoredResources.Phase model K p),
      ∃ keys : Finset ℕ,(∀ key,GeneralPaperFirstStoredResources.resident model K p phase key ≠ none → key ∈ keys) ∧
        (∑ key ∈ keys,GeneralPaperPayloadMemoryOwnership.cellSize GeneralPaperUnifiedFieldValue.encode
          (GeneralPaperFirstStoredResources.resident model K p phase) key)+
          GeneralPaperFirstStoredResources.window model K p phase < 2^word K p := by
  obtain ⟨K,hK,hSafe⟩ := uniform_capacity model hFast
  refine ⟨K,hK,fun p phase => ?_⟩
  obtain ⟨keys,hSupport,hBound⟩ := GeneralPaperFirstStoredResources.all_phases model K hK p phase
  refine ⟨keys,hSupport,hBound.trans_lt ?_⟩
  have h := hSafe p
  dsimp only [envelope] at h
  omega

end Blotto.GeneralPaperFirstStoredCapacity
