import Blotto.GeneralPaperTwoPoolLayoutLifetime

/-! Complete layout-recursion storage grows linearly in measured extent,
up to logarithmic metadata factors. Primitive word encoding and scalar
scratch use existing actual lifetimes, and all saved price fields have
their own encoded-width bound. -/
namespace Blotto.GeneralPaperLayoutLifetimeRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

@[fun_prop]
theorem encoding_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperWordEncodingLifetime.windowProfile model (S x) (A x) (A x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  unfold GeneralPaperWordEncodingLifetime.windowProfile GeneralPaperWordEncodingLifetime.profile
    GeneralPaperWordEncodingLifetime.time GeneralPaperWordEncodingLifetime.bitListProfile
    GeneralPaperStoredWordEncoding.stepBound GeneralPaperEqualRetainedStorage.wordProfile
  fun_prop (config := {maxSteps := 30000})

@[fun_prop]
theorem local_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A M Q L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L)
    (hM : Small M L) (hQ : Small Q L) :
    Polylog (fun x => GeneralPaperSequentialLayoutLifetime.localBound model (S x) (A x) (M x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => GeneralPaperSequentialLayoutLifetime.controlCap (S x) (A x) (M x) (Q x)) L := by
    unfold GeneralPaperSequentialLayoutLifetime.controlCap
    fun_prop
  have hEncoding := encoding_rate model hFast S A L hL hS hA
  have hStep := GeneralPaperStoredPreparationWorkRates.layout_step_rate model hFast S A L hL hS hA
  unfold GeneralPaperSequentialLayoutLifetime.localBound
  fun_prop

@[fun_prop]
theorem parent_rate {α : Type*} (S I A M Q L : α → ℕ)
    (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hI : Tight I L) (hA : Tight A L)
    (hM : Small M L) (hQ : Small Q L) :
    Polylog (fun x => GeneralPaperTwoPoolLayoutLifetime.parentBound (S x) (I x) (A x) (M x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hSSmall := small_of_tight hS hL
  have hISmall := small_of_tight hI hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => GeneralPaperSequentialLayoutLifetime.controlCap (S x) (I x + A x) (M x) (Q x)) L := by
    unfold GeneralPaperSequentialLayoutLifetime.controlCap
    fun_prop
  unfold GeneralPaperTwoPoolLayoutLifetime.parentBound
  fun_prop

@[fun_prop]
theorem two_pool_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S I A Bi Bo Q r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hI : Tight I L) (hA : Tight A L) (hBi : Bound Bi r L) (hBo : Bound Bo r L)
    (hQ : Small Q L) (hrSmall : Small r L) :
    Bound (fun x => GeneralPaperTwoPoolLayoutLifetime.bound model (S x) (I x) (A x) (Bi x) (Bo x) (Q x)) r L := by
  have hiSmall := bound_small hL hBi hrSmall
  have hoSmall := bound_small hL hBo hrSmall
  have hM : Small (fun x => Bi x + Bo x) L := by fun_prop
  have hiLocal := local_rate model hFast S I (fun x => Bi x + Bo x) Q L hL hS hI hM hQ
  have hoLocal := local_rate model hFast S A (fun x => Bi x + Bo x) Q L hL hS hA hM hQ
  have hParent := parent_rate S I A (fun x => Bi x + Bo x) Q L hL hS hI hA hM hQ
  have hiB : Bound (fun x => Bi x + 1) r L := by fun_prop
  have hoB : Bound (fun x => Bo x + 1) r L := by fun_prop
  have hiWindow := bound_mul_polylog _ _ r L hiB hiLocal
  have hoWindow := bound_mul_polylog _ _ r L hoB hoLocal
  have hpWindow := rate_mono hParent hr
  simpa only [GeneralPaperTwoPoolLayoutLifetime.bound] using
    bound_add _ _ r L hL (bound_add _ _ r L hL hiWindow hoWindow) hpWindow

end Blotto.GeneralPaperLayoutLifetimeRates
