import Blotto.GeneralPaperUniformStoredComponentGrowth
import Blotto.GeneralPaperEqualCopiedPreparationCapacity

/-! Uniform encoded growth of caller owners, complete preparation prices
and final wrapper. The coefficient remains a variable in every bound. -/
namespace Blotto.GeneralPaperUniformPreparationCallerGrowth
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperEqualInputInitializerCapacity (Parameters logarithmicMeasure)
open GeneralPaperUniformPreparationParameters GeneralPaperUniformSmallComposition
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem copied_price_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => GeneralPaperEqualCopiedPipeline.price model a.coefficient a.input) logarithmicMeasure := by
  have hParent := lift_uniform model (GeneralPaperEqualCopiedPreparationResources.parentCap model)
    (GeneralPaperEqualCopiedPreparationCapacity.parent_word_growth model hFast)
  apply small_mono hParent
  intro a
  dsimp only [GeneralPaperEqualCopiedPipeline.price,GeneralPaperEqualSelectedPipeline.price,
    GeneralPaperEqualInputRates.totalPrice,GeneralPaperEqualInputRates.bitPrice,
    GeneralPaperEqualCopiedPreparationResources.parentCap,GeneralPaperEqualSelectedPreparationResources.parentCap,
    GeneralPaperEqualDispatchLifetime.parentCap,S]
  omega

theorem full_price_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => GeneralPaperCompleteStoredPipelineWork.price model a.coefficient a.input) logarithmicMeasure := by
  have hL := GeneralPaperEqualInputInitializerCapacity.measure_positive (model := model)
  have hOld := copied_price_small model hFast
  have hNew := GeneralPaperUniformStoredComponentGrowth.construction_price_small model hFast
  have hS := word_small model
  have hA := small_of_tight (native_address_tight model) hL
  change Small (fun a : Parameters model => GeneralPaperEqualCopiedPipeline.price model a.coefficient a.input +
    GeneralPaperCompleteSelectedPreparationWork.bound model (S a) (source model a) +
    64 * (S a + (source model a).address + 1)) logarithmicMeasure
  fun_prop

theorem source_owners_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => GeneralPaperPreparationSourceOwners.profile model a.coefficient a.input) logarithmicMeasure := by
  have hL := GeneralPaperEqualInputInitializerCapacity.measure_positive (model := model)
  have hInitial := lift_uniform model (GeneralPaperEqualInputInitializerLifetime.profile model)
    (GeneralPaperEqualInputInitializerCapacity.uniform_word_growth model hFast)
  have hInput : Small (fun a : Parameters model => GeneralPaperEqualInputInitializerLifetime.inputProfile model (S a) a.input) logarithmicMeasure := by
    apply small_mono hInitial
    intro a
    unfold GeneralPaperEqualInputInitializerLifetime.profile
    omega
  have hCopy := lift_uniform model
    (fun W _K p => GeneralPaperEqualSelectedCopyLifetime.profile W p.n p.k (rationalWordWidth p.budget))
    (GeneralPaperEqualSelectedCopyLifetimeRates.uniform_word_growth model)
  change Small (fun a : Parameters model => GeneralPaperEqualInputInitializerLifetime.inputProfile model (S a) a.input +
    2 * GeneralPaperEqualSelectedCopyLifetime.profile (S a) a.input.n a.input.k (rationalWordWidth a.input.budget)) logarithmicMeasure
  fun_prop

theorem controls_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => GeneralPaperPreparationCallerControls.profile model a.coefficient a.input) logarithmicMeasure := by
  have hL := GeneralPaperEqualInputInitializerCapacity.measure_positive (model := model)
  have hS := word_small model
  have hK := coefficient_small model
  have hA := small_of_tight (native_address_tight model) hL
  have hn := GeneralPaperEqualInputInitializerCapacity.lift_small model (fun p => p.n) (count_small model)
  have hk := GeneralPaperEqualInputInitializerCapacity.lift_tight model (fun p => p.k) (exponent_tight model)
  have hkSmall := small_of_tight hk hL
  have hP := full_price_small model hFast
  have hCap : Small (fun a : Parameters model => GeneralPaperPreparationCallerControls.cap model a.coefficient a.input) logarithmicMeasure := by
    change Small (fun a : Parameters model => S a + a.coefficient + a.input.n + a.input.k + (source model a).address +
      GeneralPaperCompleteStoredPipelineWork.price model a.coefficient a.input + 1) logarithmicMeasure
    fun_prop
  have hBits := small_of_tight (tight_bits _ logarithmicMeasure hL hCap) hL
  change Small (fun a : Parameters model => 10 * (GeneralPaperEncodedScalarStorage.natBits
    (GeneralPaperPreparationCallerControls.cap model a.coefficient a.input) + S a) + 256 * S a) logarithmicMeasure
  fun_prop

theorem result_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => GeneralPaperPreparationCallerLifetime.resultProfile model a.coefficient a.input) logarithmicMeasure := by
  have hL := GeneralPaperEqualInputInitializerCapacity.measure_positive (model := model)
  have hLM : ∀ a : Parameters model,logarithmicMeasure a ≤ M a := fun _ => Nat.le_add_right _ _
  have hP := small_log_mono (full_price_small model hFast) hLM
  have hUnit := GeneralPaperMeasuredPlanLifetimeRates.unit_rate model hFast S
    (fun a => (source model a).address) (fun a => GeneralPaperCompleteStoredPipelineWork.price model a.coefficient a.input)
    M scale_positive (word_tight_scale model) (tight_log_mono (native_address_tight model) hLM) hP
  exact bound_small_scale hL hUnit (small_constant 1 _ hL) (scale_small model)

theorem caller_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => GeneralPaperPreparationCallerLifetime.profile model a.coefficient a.input) logarithmicMeasure := by
  exact small_add _ _ _ (small_add _ _ _ (source_owners_small model hFast) (controls_small model hFast)) (result_small model hFast)

end Blotto.GeneralPaperUniformPreparationCallerGrowth
