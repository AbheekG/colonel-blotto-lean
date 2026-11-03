import Blotto.GeneralPaperStoredDispatchLoadWork

/-! Outer address/marker access and pointer decoding are polylogarithmic
in the draw logarithm when the actual outer address width is logarithmic. -/
namespace Blotto.GeneralPaperStoredOuterWorkRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem marker_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredOuterReadWork.markerBound model (A x)) L := by
  have hAP := polylog_of_tight hA
  unfold GeneralPaperStoredOuterReadWork.markerBound
  fun_prop

theorem grouped_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredDispatchLoadWork.groupedBound model (A x)) L := by
  have hAP := polylog_of_tight hA
  have hAS := small_of_tight hA hL
  have hBits := polylog_bits A L hL hAS
  have hStep : Polylog (fun x => GeneralPaperStoredWordEncoding.stepBound model (A x) (A x) (A x + 1)) L := by
    unfold GeneralPaperStoredWordEncoding.stepBound
    fun_prop
  unfold GeneralPaperStoredDispatchLoadWork.groupedBound GeneralPaperStoredDispatchLoadWork.dominantBound
    GeneralPaperStoredDispatchLoadWork.encodeBound GeneralPaperStoredOuterReadWork.addressBound
  fun_prop

theorem dominant_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredDispatchLoadWork.dominantBound model (A x)) L :=
  dominated (grouped_rate model hFast A L hL hA) (fun x => by unfold GeneralPaperStoredDispatchLoadWork.groupedBound; omega)

end Blotto.GeneralPaperStoredOuterWorkRates
