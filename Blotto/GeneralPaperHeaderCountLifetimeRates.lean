import Blotto.GeneralPaperHeaderCountDirectoryLifetime

/-! Count preparation has uniform extent-linear fast-bit storage rates.
Actual local header mass is summed once, and global extent/work appear
only inside encoded metadata factors. -/
namespace Blotto.GeneralPaperHeaderCountLifetimeRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperHeaderTargetCopyLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[fun_prop]
theorem encoding_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperWordEncodingLifetime.windowProfile model (S x) (A x) (A x + 8)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  unfold GeneralPaperWordEncodingLifetime.windowProfile GeneralPaperWordEncodingLifetime.profile
    GeneralPaperWordEncodingLifetime.time GeneralPaperWordEncodingLifetime.bitListProfile
    GeneralPaperStoredWordEncoding.stepBound GeneralPaperEqualRetainedStorage.wordProfile
  fun_prop (config := {maxSteps := 30000})

@[fun_prop]
theorem unit_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B Q L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L)
    (hB : Small B L) (hQ : Small Q L) :
    Polylog (fun x => GeneralPaperHeaderCountExpansionLifetime.unit model (S x) (A x) (B x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => cap (S x) (A x) (B x) (Q x)) L := by unfold cap; fun_prop
  have hCopy := GeneralPaperHeaderTargetCopyLifetime.unit_rate model hFast S A B Q L hL hS hA hB hQ
  have hEncoding := encoding_rate model hFast S A L hL hS hA
  have hPadding := GeneralPaperHeaderWordLoopsLifetime.padding_unit_rate S A B Q L hL hS hA hB hQ
  have hAppend := GeneralPaperHeaderWordLoopsLifetime.append_unit_rate S A Q L hL hS hA hQ
  unfold GeneralPaperHeaderCountExpansionLifetime.unit GeneralPaperHeaderCountExpansionLifetime.commonUnit
    GeneralPaperHeaderCountExpansionLifetime.positiveUnit GeneralPaperMeasuredLayoutStorage.regionBound
  fun_prop

@[fun_prop]
theorem frame_unit_rate {α : Type*} (S A B Q L : α → ℕ) (hL : ∀ x,1 ≤ L x)
    (hS : Tight S L) (hA : Tight A L) (hB : Small B L) (hQ : Small Q L) :
    Polylog (fun x => GeneralPaperHeaderCountDirectoryLifetime.frameUnit (S x) (A x) (B x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => cap (S x) (A x) (B x) (Q x)) L := by unfold cap; fun_prop
  unfold GeneralPaperHeaderCountDirectoryLifetime.frameUnit
  fun_prop

theorem profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => GeneralPaperHeaderCountDirectoryLifetime.profile model (S x) (A x) (B x)) r L := by
  let Q := fun x => GeneralPaperStoredDirectoryPreparationWork.countBound model (S x) (A x) (B x)
  have hAllWork := GeneralPaperStoredPreparationWorkRates.directory_rate model hFast S A B r L hL hr hS hA hB
  have hCountWork : Bound Q r L := by
    apply dominated hAllWork
    intro x
    unfold Q GeneralPaperStoredDirectoryPreparationWork.bound
    omega
  have hQ := bound_small hL hCountWork hrSmall
  have hBSmall := bound_small hL hB hrSmall
  have hUnit := unit_rate model hFast S A B Q L hL hS hA hBSmall hQ
  have hFrameUnit := frame_unit_rate S A B Q L hL hS hA hBSmall hQ
  have hTwiceB : Bound (fun x => 2 * B x) r L := by fun_prop
  have hCount : Bound (fun x => B x + 1) r L := by fun_prop
  have hExpansion := bound_mul_polylog _ _ r L hTwiceB hUnit
  have hFrames := bound_mul_polylog _ _ r L hCount hFrameUnit
  have hOwners := GeneralPaperMeasuredDirectoryStorageRates.count_rate model hFast S A B r L hL hr hS hA hB hrSmall
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => cap (S x) (A x) (B x) (Q x)) L := by unfold cap; fun_prop
  have hRegion : Bound (fun x => GeneralPaperMeasuredLayoutStorage.regionBound (S x) (A x)) r L := by
    unfold GeneralPaperMeasuredLayoutStorage.regionBound
    fun_prop
  have hParent : Bound (fun x => 5 * (GeneralPaperEncodedScalarStorage.natBits (cap (S x) (A x) (B x) (Q x)) + S x) + 160 * S x) r L := by fun_prop
  simpa only [GeneralPaperHeaderCountDirectoryLifetime.profile,Q,Nat.add_assoc] using
    bound_add _ _ r L hL (bound_add _ _ r L hL (bound_add _ _ r L hL hOwners hExpansion) hFrames)
      (bound_add _ _ r L hL hRegion hParent)

end Blotto.GeneralPaperHeaderCountLifetimeRates
