import Blotto.GeneralPaperStoredDominantEmissionWork

/-! Address-only read overhead is polylogarithmic whenever the retained
address width is logarithmic. Dominant full-row payload work is additive in
the original budget encoding; no longest-input-times-field-count term enters. -/
namespace Blotto.GeneralPaperStoredReadWorkRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192

@[fun_prop]
theorem reference_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredReferenceReadWork.readBound model (A x) (A x)) L := by
  have hAP := polylog_of_tight hA
  have hAS := small_of_tight hA hL
  dsimp only [GeneralPaperStoredReferenceReadWork.readBound,GeneralPaperStoredReferenceReadWork.slotBound,
    GeneralPaperStoredReferenceReadWork.envelope,GeneralPaperStoredWordEncoding.stepBound]
  fun_prop (config := {maxSteps := 30000})

@[fun_prop]
theorem scalar_overhead_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredScalarReadWork.overhead model (A x)) L := by
  have hAP := polylog_of_tight hA
  unfold GeneralPaperStoredScalarReadWork.overhead
  fun_prop

@[fun_prop]
theorem step_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredStreamWork.stepBound model (A x)) L := by
  have hAP := polylog_of_tight hA
  have hAS := small_of_tight hA hL
  unfold GeneralPaperStoredStreamWork.stepBound
  fun_prop

@[fun_prop]
theorem per_element_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredRationalCollectionWork.perElement model (A x)) L := by
  have hAP := polylog_of_tight hA
  unfold GeneralPaperStoredRationalCollectionWork.perElement
  fun_prop

@[fun_prop]
theorem count_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredCountReadWork.bound model (A x)) L := by
  have hAP := polylog_of_tight hA
  unfold GeneralPaperStoredCountReadWork.bound
  fun_prop

theorem dominant_vertex_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A n b r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hA : Tight A L) (hn : Bound n r L) (hb : Bound b r L) :
    Bound (fun x => GeneralPaperStoredDominantEmissionWork.vertexBound model (A x) (n x) (b x)) r L := by
  have hAP := polylog_of_tight hA
  have hCount : Bound (fun x => GeneralPaperStoredCountReadWork.bound model (A x)) r L :=
    rate_mono (count_rate model hFast A L hL hA) hr
  have hReference : Bound (fun x => GeneralPaperStoredReferenceReadWork.readBound model (A x) (A x)) r L :=
    rate_mono (reference_rate model hFast A L hL hA) hr
  unfold GeneralPaperStoredDominantEmissionWork.vertexBound
  fun_prop (config := {maxSteps := 30000})

end Blotto.GeneralPaperStoredReadWorkRates
