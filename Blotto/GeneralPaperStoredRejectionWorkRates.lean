import Blotto.GeneralPaperStoredNativeRejectionBound

/-! With seven retained categorical rows, complete actual rejection work
is linear in the short range-word bound up to logarithmic address factors.
The actual operation bounds, native seven-row instantiation and growth
algebra refer to the same per-attempt and one-time-entry majorants. -/
namespace Blotto.GeneralPaperStoredRejectionWorkRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

theorem fixed_count_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A w r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hA : Tight A L) (hw : Bound w r L) :
    Bound (fun x => GeneralPaperStoredSamplerRejectionWork.expectedBound model (A x) (w x) 7 7) r L := by
  have hAP := polylog_of_tight hA
  have hPlus : Bound (fun x => w x + 1) r L := by fun_prop
  have hFresh := GeneralPaperStoredBooleanWorkRates.fresh_rate model hFast A w r L hL hr hA hw
  have hWord := GeneralPaperStoredBooleanWorkRates.word_rate model hFast A (fun x => w x + 1) r L hL hr hA hPlus
  have hDenom := GeneralPaperStoredBooleanWorkRates.denominator_rate model hFast A (fun x => w x + 1) r L hL hr hA hPlus
  have hRuler : Bound (fun x => GeneralPaperStoredRulerReadWork.bound model (A x)) r L :=
    rate_mono (GeneralPaperStoredBooleanWorkRates.ruler_rate model hFast A L hL hA) hr
  have hCount : Bound (fun x => GeneralPaperStoredCountReadWork.bound model (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.count_rate model hFast A L hL hA) hr
  have hReference : Bound (fun x => GeneralPaperStoredReferenceReadWork.readBound model (A x) (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.reference_rate model hFast A L hL hA) hr
  have hStep : Bound (fun x => GeneralPaperStoredStreamWork.stepBound model (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.step_rate model hFast A L hL hA) hr
  unfold GeneralPaperStoredSamplerRejectionWork.expectedBound GeneralPaperStoredSamplerRejectionWork.entryBound
    GeneralPaperStoredRejectionWork.perAttempt GeneralPaperStoredTrialWork.bound GeneralPaperStoredCacheCategoricalWork.bound
    GeneralPaperStoredCategoricalWork.bound GeneralPaperStoredCategoricalWork.perRow GeneralPaperStoredBooleanRowsWork.bound
  fun_prop (config := {maxSteps := 5000})

theorem logarithmic_word_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A w L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) (hw : Tight w L) :
    Polylog (fun x => GeneralPaperStoredSamplerRejectionWork.expectedBound model (A x) (w x) 7 7) L :=
  fixed_count_rate model hFast A w (fun _ => 1) L hL (fun _ => le_rfl) hA (polylog_of_tight hw)

end Blotto.GeneralPaperStoredRejectionWorkRates
