import Blotto.GeneralPaperStoredSamplerMidpointWork
import Blotto.GeneralPaperStoredBooleanWorkRates

/-! Complete stored midpoint work is polylogarithmic when the address,
fresh-bit count and retained control widths are linear in the draw logarithm.
These rates concern the same majorants used for the actual runtime. -/
namespace Blotto.GeneralPaperStoredMidpointWorkRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem decoder_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A K L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) (hK : Tight K L) :
    Polylog (fun x => GeneralPaperStoredFreshDecoderWork.bound model (A x) (K x)) L := by
  have hAP := polylog_of_tight hA
  have hKP := polylog_of_tight hK
  have hPlus : Tight (fun x => K x + 1) L := by fun_prop
  have hMetadata : Tight (fun x => 2 * (K x + 1) + 4) L := by fun_prop
  have hWord := polylog_word _ L (small_of_tight hPlus hL)
  have hMeta := polylog_word _ L (small_of_tight hMetadata hL)
  have hFresh : Polylog (fun x => GeneralPaperStoredFreshWork.bound model (A x) (K x) 0) L :=
    GeneralPaperStoredBooleanWorkRates.fresh_rate model hFast A K (fun _ => 1) L hL (fun _ => le_rfl) hA hKP
  unfold GeneralPaperStoredFreshDecoderWork.bound GeneralPaperStoredFreshDecoderWork.decodeBound
  fun_prop

theorem controls_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A P L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) (hP : Tight P L) :
    Polylog (fun x => GeneralPaperStoredPreparedReadWork.controlsMajorant model (A x) (P x)) L := by
  have hAP := polylog_of_tight hA
  have hPP := polylog_of_tight hP
  have hScalar := GeneralPaperStoredReadWorkRates.scalar_overhead_rate model hFast A L hL hA
  have hStep := GeneralPaperStoredReadWorkRates.step_rate model hFast A L hL hA
  unfold GeneralPaperStoredPreparedReadWork.controlsMajorant GeneralPaperStoredNaturalCollectionWork.perElement
  fun_prop

theorem sampler_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A P K L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) (hP : Tight P L) (hK : Tight K L) :
    Polylog (fun x => GeneralPaperStoredSamplerMidpointWork.majorant model (A x) (P x) (K x)) L := by
  have hAP := polylog_of_tight hA
  have hControls := controls_rate model hFast A P L hL hA hP
  have hDecoder := decoder_rate model hFast A K L hL hA hK
  have hHeight : Tight (fun x => 1 + 2 * GeneralPaperCachedMidpointAssembly.height (K x)) L := by
    have hMajor : Tight (fun x => 16 * K x + 47) L := by fun_prop
    have hEq : (fun x => 1 + 2 * GeneralPaperCachedMidpointAssembly.height (K x)) = (fun x => 16 * K x + 47) := by
      funext x
      unfold GeneralPaperCachedMidpointAssembly.height expressionHeightBudget
      norm_num only
      omega
    rw [hEq]
    exact hMajor
  have hHeightP := polylog_of_tight hHeight
  have hSmall := small_of_tight hHeight hL
  have hArithmetic := rational_polylog model hFast _ L hL hHeightP hSmall
  unfold GeneralPaperStoredSamplerMidpointWork.majorant
  fun_prop

end Blotto.GeneralPaperStoredMidpointWorkRates
