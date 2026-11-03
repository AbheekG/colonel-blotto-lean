import Blotto.GeneralPaperUniformPreparationParameters

/-! Full stored-constructor component reserves have uniform encoded growth
while the actual preparation coefficient varies with the parameter domain.
The larger rate scale is eliminated before coefficient calibration. -/
namespace Blotto.GeneralPaperUniformStoredComponentGrowth
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperEqualInputInitializerCapacity (Parameters logarithmicMeasure)
open GeneralPaperUniformPreparationParameters
open GeneralPaperUniformSmallComposition
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem combined_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => GeneralPaperSelectedOuterInputLifetime.combinedBound model (S a) (source model a)) logarithmicMeasure := by
  let R := fun a : Parameters model => GeneralPaperEqualSelectedDescription.footprint (source model a) + 1
  have hL := GeneralPaperEqualInputInitializerCapacity.measure_positive (model := model)
  have hLM : ∀ a : Parameters model,logarithmicMeasure a ≤ M a := fun _ => Nat.le_add_right _ _
  have hR : Small R logarithmicMeasure := small_add _ _ _ (description_small model) (small_constant 1 _ hL)
  have hRM := small_log_mono hR hLM
  have hA := tight_log_mono (native_address_tight model) hLM
  have hExtent : Bound (fun a : Parameters model => GeneralPaperEqualSelectedDescription.footprint (source model a)) R M :=
    pointwise _ _ _ 1 (fun a => by dsimp only [R]; omega)
  have hInnerCap : ∀ a : Parameters model,
      (GeneralPaperEqualMeasuredLayout.inner model (S a) (source model a)).sizes.sum <
        2 ^ GeneralPaperEqualMeasuredLayout.innerWidth (source model a) := fun a =>
    GeneralPaperEqualMeasuredLayout.inner_capacity model (S a) (S a) a.input.k a.input.values a.input.selector
      a.input.correct a.input.budget (source model a)
  have hOuterCap : ∀ a : Parameters model,
      (GeneralPaperEqualMeasuredLayout.outer model (S a) (source model a)).sizes.sum <
        2 ^ (source model a).address := by
    intro a
    have h := GeneralPaperEqualMeasuredLayout.total_capacity model (S a) (S a) a.input.k a.input.values
      a.input.selector a.input.correct a.input.budget (source model a)
    exact (Nat.le_add_left _ _).trans_lt h
  have hBound := GeneralPaperSelectedPreparationGenericRates.combined_rate model hFast S R M
    (fun a => a.input.n) (fun a => a.input.k)
    (fun a => GeneralPaperEqualNativeSampler.rounded true model (S a) a.input.k a.input.values a.input.selector a.input.correct)
    (fun a => a.input.budget) (source model) scale_positive (fun a => by dsimp only [R]; omega)
    (word_tight_scale model) hA hExtent hRM hInnerCap hOuterCap
  exact bound_small_scale hL hBound hR (scale_small model)

theorem construction_price_small (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => GeneralPaperCompleteSelectedPreparationWork.bound model (S a) (source model a)) logarithmicMeasure := by
  let R := fun a : Parameters model => GeneralPaperEqualSelectedDescription.footprint (source model a) + 1
  have hL := GeneralPaperEqualInputInitializerCapacity.measure_positive (model := model)
  have hR : Small R logarithmicMeasure := small_add _ _ _ (description_small model) (small_constant 1 _ hL)
  have hA := tight_log_mono (native_address_tight model) (fun a : Parameters model => show logarithmicMeasure a ≤ M a from Nat.le_add_right _ _)
  have hBound := GeneralPaperCompleteSelectedPreparationWork.rate model hFast S R M
    (fun a => a.input.n) (fun a => a.input.k)
    (fun a => GeneralPaperEqualNativeSampler.rounded true model (S a) a.input.k a.input.values a.input.selector a.input.correct)
    (fun a => a.input.budget) (source model) scale_positive (fun a => by dsimp only [R]; omega)
    (word_tight_scale model) hA
    (pointwise _ _ _ 1 (fun a => by
      change GeneralPaperEqualSelectedDescription.footprint (source model a) ≤ 1 * R a
      simpa only [Nat.one_mul] using Nat.le_add_right (GeneralPaperEqualSelectedDescription.footprint (source model a)) 1))
  exact bound_small_scale hL hBound hR (scale_small model)

end Blotto.GeneralPaperUniformStoredComponentGrowth
