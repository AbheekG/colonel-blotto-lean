import Blotto.GeneralPaperUniformPreparationCallerGrowth

/-! One global coefficient covers the complete preparation phase reserve,
resident memory, all enclosing caller controls and the full work price.
Execution constructs its word from that fixed coefficient and input size;
it never evaluates this erased envelope to choose an address width. -/
namespace Blotto.GeneralPaperStoredPreparationUniformCapacity
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperEqualInputInitializerCapacity (Parameters logarithmicMeasure)
open GeneralPaperUniformPreparationParameters GeneralPaperUniformSmallComposition
open GeneralPaperUniformPreparationCallerGrowth
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

noncomputable def envelope (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperStoredPreparationPhases.profile model K p + GeneralPaperPreparationCallerControls.cap model K p + 1

theorem profile_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => GeneralPaperStoredPreparationPhases.profile model a.coefficient a.input) logarithmicMeasure := by
  have hDescription := description_small model
  have hSource := lift_uniform model (GeneralPaperEqualSelectedPreparationResources.profile model)
    (GeneralPaperEqualSelectedPreparationCapacity.uniform_word_growth model hFast)
  have hCopy := lift_uniform model
    (fun W _K p => GeneralPaperEqualSelectedCopyLifetime.profile W p.n p.k (rationalWordWidth p.budget))
    (GeneralPaperEqualSelectedCopyLifetimeRates.uniform_word_growth model)
  have hCaller := caller_small model hFast
  have hComponents := GeneralPaperUniformStoredComponentGrowth.combined_small model hFast
  exact small_add _ _ _ hDescription
    (small_add _ _ _ (small_add _ _ _ hSource hCopy) (small_add _ _ _ hCaller hComponents))

theorem caller_cap_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => GeneralPaperPreparationCallerControls.cap model a.coefficient a.input) logarithmicMeasure := by
  have hL := GeneralPaperEqualInputInitializerCapacity.measure_positive (model := model)
  have hS := word_small model
  have hK := coefficient_small model
  have hA := small_of_tight (native_address_tight model) hL
  have hn := GeneralPaperEqualInputInitializerCapacity.lift_small model (fun p => p.n) (count_small model)
  have hk := GeneralPaperEqualInputInitializerCapacity.lift_tight model (fun p => p.k) (exponent_tight model)
  have hkSmall := small_of_tight hk hL
  have hP := full_price_small model hFast
  change Small (fun a : Parameters model => S a + a.coefficient + a.input.n + a.input.k + (source model a).address +
    GeneralPaperCompleteStoredPipelineWork.price model a.coefficient a.input + 1) logarithmicMeasure
  fun_prop

theorem envelope_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => envelope model a.coefficient a.input) logarithmicMeasure :=
  small_add _ _ _ (small_add _ _ _ (profile_small model hFast) (caller_cap_small model hFast))
    (small_constant 1 _ GeneralPaperEqualInputInitializerCapacity.measure_positive)

theorem uniform_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ,1 ≤ K ∧ ∀ p : Input model,envelope model K p < 2 ^ word K p := by
  obtain ⟨C,hC⟩ := envelope_small model hFast
  exact GeneralPaperSelfReferenceCapacity.uniform_capacity (fun _W K p => envelope model K p)
    logarithm logarithm_positive ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

theorem all_phases_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ,1 ≤ K ∧ ∀ (p : Input model) (phase : GeneralPaperStoredPreparationPhases.Phase model K p),
      ∃ keys : Finset ℕ,(∀ key,GeneralPaperStoredPreparationPhases.resident model K p phase key ≠ none → key ∈ keys) ∧
        (∑ key ∈ keys,cellSize encode (GeneralPaperStoredPreparationPhases.resident model K p phase) key) +
          GeneralPaperStoredPreparationPhases.window model K p phase < 2 ^ word K p ∧
        (∀ value ∈ GeneralPaperPreparationCallerControls.controls model K p,value < 2 ^ word K p) ∧
        GeneralPaperCompleteStoredPipelineWork.price model K p < 2 ^ word K p := by
  obtain ⟨K,hK,hSafe⟩ := uniform_capacity model hFast
  refine ⟨K,hK,fun p phase => ?_⟩
  obtain ⟨keys,hSupport,hBound⟩ := GeneralPaperStoredPreparationPhases.all_phases model K hK p phase
  have hProfile : GeneralPaperStoredPreparationPhases.profile model K p < 2 ^ word K p := by
    have h := hSafe p
    dsimp only [envelope] at h
    omega
  have hCap : GeneralPaperPreparationCallerControls.cap model K p < 2 ^ word K p := by
    have h := hSafe p
    dsimp only [envelope] at h
    omega
  refine ⟨keys,hSupport,hBound.trans_lt hProfile,
    fun value hv => (GeneralPaperPreparationCallerControls.fields_bounded model K p value hv).trans_lt hCap,?_⟩
  apply lt_of_le_of_lt _ hCap
  unfold GeneralPaperPreparationCallerControls.cap
  omega

end Blotto.GeneralPaperStoredPreparationUniformCapacity
