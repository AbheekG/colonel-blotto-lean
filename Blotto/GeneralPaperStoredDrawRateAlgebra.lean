import Blotto.GeneralPaperStoredDrawMajorant
import Blotto.GeneralPaperStoredMidpointWorkRates
import Blotto.GeneralPaperStoredRejectionWorkRates

/-! Fixed-depth rational heights retain linear precision dependence. These
growth rules distinguish an operand's size from its logarithmic encoding. -/
namespace Blotto.GeneralPaperStoredDrawRateAlgebra
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

@[fun_prop]
theorem expression_bound {α : Type*} (s r L : α → ℕ) (d : ℕ)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hs : Bound s r L) :
    Bound (fun x => expressionHeightBudget (s x) d) r L := by
  have hMajor : Bound (fun x => (2 ^ d) * (s x + 1)) r L := by fun_prop
  apply dominated hMajor
  intro x
  unfold expressionHeightBudget
  exact (Nat.sub_le _ _).trans_eq (Nat.mul_comm _ _)

@[fun_prop]
theorem expression_small {α : Type*} (s L : α → ℕ) (d : ℕ)
    (hL : ∀ x,1 ≤ L x) (hs : Small s L) :
    Small (fun x => expressionHeightBudget (s x) d) L := by
  have hMajor : Small (fun x => (2 ^ d) * (s x + 1)) L := by fun_prop
  apply small_mono hMajor
  intro x
  unfold expressionHeightBudget
  exact (Nat.sub_le _ _).trans_eq (Nat.mul_comm _ _)

theorem decoder_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A K r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hA : Tight A L) (hK : Bound K r L) (hKs : Small K L) :
    Bound (fun x => GeneralPaperStoredFreshDecoderWork.bound model (A x) (K x)) r L := by
  have hAP := polylog_of_tight hA
  have hPlus : Small (fun x => K x + 1) L := by fun_prop
  have hMetadata : Small (fun x => 2 * (K x + 1) + 4) L := by fun_prop
  have hWord := polylog_word _ L hPlus
  have hMeta := polylog_word _ L hMetadata
  have hFresh := GeneralPaperStoredBooleanWorkRates.fresh_rate model hFast A K r L hL hr hA hK
  unfold GeneralPaperStoredFreshDecoderWork.bound GeneralPaperStoredFreshDecoderWork.decodeBound
  fun_prop

theorem midpoint_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A P K r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hA : Tight A L) (hP : Bound P r L) (hK : Bound K r L) (hKs : Small K L) :
    Bound (fun x => GeneralPaperStoredSamplerMidpointWork.majorant model (A x) (P x) (K x)) r L := by
  have hAP := polylog_of_tight hA
  have hDecoder := decoder_rate model hFast A K r L hL hr hA hK hKs
  have hCount : Bound (fun x => GeneralPaperStoredCountReadWork.bound model (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.count_rate model hFast A L hL hA) hr
  have hReference : Bound (fun x => GeneralPaperStoredReferenceReadWork.readBound model (A x) (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.reference_rate model hFast A L hL hA) hr
  have hScalar : Bound (fun x => GeneralPaperStoredScalarReadWork.overhead model (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.scalar_overhead_rate model hFast A L hL hA) hr
  have hStep : Bound (fun x => GeneralPaperStoredStreamWork.stepBound model (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.step_rate model hFast A L hL hA) hr
  have hHeight : Bound (fun x => 1 + 2 * GeneralPaperCachedMidpointAssembly.height (K x)) r L := by
    unfold GeneralPaperCachedMidpointAssembly.height
    fun_prop
  have hHeightSmall : Small (fun x => 1 + 2 * GeneralPaperCachedMidpointAssembly.height (K x)) L := by
    unfold GeneralPaperCachedMidpointAssembly.height
    fun_prop
  have hArithmetic := rational_bound model hFast _ r L hL hHeight hHeightSmall
  unfold GeneralPaperStoredSamplerMidpointWork.majorant GeneralPaperStoredPreparedReadWork.controlsMajorant
    GeneralPaperStoredNaturalCollectionWork.perElement
  fun_prop

end Blotto.GeneralPaperStoredDrawRateAlgebra
