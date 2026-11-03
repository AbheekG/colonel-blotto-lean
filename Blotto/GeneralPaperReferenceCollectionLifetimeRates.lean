import Blotto.GeneralPaperDirectoryReferenceCollectionLifetime

/-! Complete reference collection has extent-linear uniform fast-bit
storage rates. Positions are included in source entries; saved work values
contribute only their encoded widths. -/
namespace Blotto.GeneralPaperReferenceCollectionLifetimeRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperStoredReferenceReadWork (envelope slotBound)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[fun_prop]
theorem slot_profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperReferenceSlotLifetime.profile model (S x) (A x) (A x + 8)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hEnvelope : Polylog (fun x => envelope (A x + 8)) L := by unfold envelope; fun_prop
  have hEnvelopeSmall := small_of_polylog hL hEnvelope
  have hSlot : Polylog (fun x => slotBound model (S x) (A x) (A x + 8)) L := by
    unfold slotBound GeneralPaperStoredWordEncoding.stepBound
    fun_prop (config := {maxSteps := 30000})
  have hSlotSmall := small_of_polylog hL hSlot
  have hEncoding : Polylog (fun x => GeneralPaperWordEncodingLifetime.windowProfile model (S x) (A x) (envelope (A x + 8))) L := by
    unfold GeneralPaperWordEncodingLifetime.windowProfile GeneralPaperWordEncodingLifetime.profile
      GeneralPaperWordEncodingLifetime.time GeneralPaperWordEncodingLifetime.bitListProfile
      GeneralPaperStoredWordEncoding.stepBound GeneralPaperEqualRetainedStorage.wordProfile
    fun_prop (config := {maxSteps := 30000})
  have hRat := rational_polylog model hFast (fun x => envelope (A x + 8)) L hL hEnvelope hEnvelopeSmall
  have hSlotBits := polylog_bits (fun x => slotBound model (S x) (A x) (A x + 8)) L hL hSlotSmall
  have hSBits := polylog_bits S L hL hSSmall
  have hLimit : Polylog (fun x => GeneralPaperReferenceSlotLifetime.wordLimit model (S x) (A x) (A x + 8)) L := by
    unfold GeneralPaperReferenceSlotLifetime.wordLimit
    exact polylog_add _ _ L hL (polylog_add _ _ L hL (polylog_add _ _ L hL hEnvelope hSlotBits) hSBits)
      (polylog_constant 1 L)
  have hScale (c : ℕ) (f : α → ℕ) (hf : Polylog f L) : Polylog (fun x => c * f x) L :=
    polylog_mul _ _ L (polylog_constant c L) hf
  have h0 := hScale 160 _ (polylog_add _ _ L hL
    (polylog_add _ _ L hL (hScale 5 _ hRat) (hScale 16 _ hSP)) (polylog_constant 16 L))
  have h1 := hScale 2 _ hAP
  have h2 := hScale 64 _ hSP
  have h3 := hScale 14 _ (polylog_add _ _ L hL hLimit hSP)
  have h4 := hScale 288 _ hSP
  exact polylog_add _ _ L hL
    (polylog_add _ _ L hL (polylog_add _ _ L hL (polylog_add _ _ L hL
      (polylog_add _ _ L hL (polylog_add _ _ L hL h0 hEncoding) hEnvelope) h1) h2) h3) h4

@[fun_prop]
theorem batch_unit_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A Q L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) (hQ : Small Q L) :
    Polylog (fun x => GeneralPaperReferenceBatchLifetime.unit model (S x) (A x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hSlot := slot_profile_rate model hFast S A L hL hS hA
  have hScalar := GeneralPaperStoredPreparationWorkRates.scalar_rate model hFast S A L hL hS hA
  unfold GeneralPaperReferenceBatchLifetime.unit GeneralPaperReferenceBatchLifetime.frameUnit
    GeneralPaperReferenceBatchLifetime.wordLimit
  fun_prop

@[fun_prop]
theorem append_unit_rate {α : Type*} (S A Q L : α → ℕ) (hL : ∀ x,1 ≤ L x)
    (hS : Tight S L) (hA : Tight A L) (hQ : Small Q L) :
    Polylog (fun x => GeneralPaperReferenceCollectionLifetime.appendUnit (S x) (A x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hFrame := GeneralPaperUnifiedInstallationLifetime.lift_frame_rate S A Q L hL hS hA hQ
  unfold GeneralPaperReferenceCollectionLifetime.appendUnit
  fun_prop

@[fun_prop]
theorem unit_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A Q L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) (hQ : Small Q L) :
    Polylog (fun x => GeneralPaperReferenceCollectionLifetime.unit model (S x) (A x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hBatch := batch_unit_rate model hFast S A Q L hL hS hA hQ
  have hAppend := append_unit_rate S A Q L hL hS hA hQ
  unfold GeneralPaperReferenceCollectionLifetime.unit GeneralPaperReferenceCollectionLifetime.frameUnit
    GeneralPaperReferenceBatchLifetime.wordLimit
  fun_prop

theorem profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => GeneralPaperDirectoryReferenceCollectionLifetime.profile model (S x) (A x) (B x)) r L := by
  let Q := fun x => GeneralPaperStoredDirectoryPreparationWork.installBound model (S x) (A x) (B x)
  have hAllWork := GeneralPaperStoredPreparationWorkRates.directory_rate model hFast S A B r L hL hr hS hA hB
  have hInstallWork : Bound Q r L := by
    apply dominated hAllWork
    intro x
    unfold Q GeneralPaperStoredDirectoryPreparationWork.bound
    omega
  have hQ := bound_small hL hInstallWork hrSmall
  have hUnit := unit_rate model hFast S A Q L hL hS hA hQ
  have hCount : Bound (fun x => 2 * B x + 1) r L := by fun_prop
  exact bound_mul_polylog _ _ r L hCount hUnit

end Blotto.GeneralPaperReferenceCollectionLifetimeRates
