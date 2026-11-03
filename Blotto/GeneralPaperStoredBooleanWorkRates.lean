import Blotto.GeneralPaperStoredDenominatorWork

/-! Boolean collection, word reconstruction and fresh-bit countdown work
are linear in their counts up to logarithmic address factors. These are
component rates; the full reached-row categorical/rejection join is separate. -/
namespace Blotto.GeneralPaperStoredBooleanWorkRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192

@[fun_prop]
theorem bits_per_element {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredBitCollectionWork.perElement model (A x)) L := by
  have hAP := polylog_of_tight hA
  unfold GeneralPaperStoredBitCollectionWork.perElement
  fun_prop

@[fun_prop]
theorem bits_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A w r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hA : Tight A L) (hw : Bound w r L) :
    Bound (fun x => GeneralPaperStoredBitCollectionWork.bound model (A x) (w x)) r L := by
  have hAP := polylog_of_tight hA
  have hCount : Bound (fun x => GeneralPaperStoredCountReadWork.bound model (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.count_rate model hFast A L hL hA) hr
  unfold GeneralPaperStoredBitCollectionWork.bound
  fun_prop

theorem nat_bits_bound {α : Type*} (w r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hw : Bound w r L) :
    Bound (fun x => GeneralPaperEncodedScalarStorage.natBits (w x)) r L := by
  have hMajor : Bound (fun x => w x + 2) r L := by fun_prop
  apply dominated hMajor
  intro x
  have h := Nat.log2_le_self (w x)
  unfold GeneralPaperEncodedScalarStorage.natBits binaryWordWidth
  omega

@[fun_prop]
theorem word_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A w r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hA : Tight A L) (hw : Bound w r L) :
    Bound (fun x => GeneralPaperStoredBooleanWordWork.bound model (A x) (w x)) r L := by
  have hAP := polylog_of_tight hA
  have hBits := bits_rate model hFast A w r L hL hr hA hw
  have hNat := nat_bits_bound w r L hL hr hw
  have hReference : Bound (fun x => GeneralPaperStoredReferenceReadWork.readBound model (A x) (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.reference_rate model hFast A L hL hA) hr
  unfold GeneralPaperStoredBooleanWordWork.bound GeneralPaperStoredBooleanWordWork.packedBound
  fun_prop

@[fun_prop]
theorem fresh_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A w r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hA : Tight A L) (hw : Bound w r L) :
    Bound (fun x => GeneralPaperStoredFreshWork.bound model (A x) (w x) 0) r L := by
  have hAP := polylog_of_tight hA
  have hAS := small_of_tight hA hL
  unfold GeneralPaperStoredFreshWork.bound GeneralPaperStoredFreshWork.stepBound
  fun_prop

@[fun_prop]
theorem ruler_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredRulerReadWork.bound model (A x)) L := by
  have hAP := polylog_of_tight hA
  unfold GeneralPaperStoredRulerReadWork.bound
  fun_prop

@[fun_prop]
theorem denominator_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A w r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hA : Tight A L) (hw : Bound w r L) :
    Bound (fun x => GeneralPaperStoredDenominatorWork.bound model (A x) (w x)) r L := by
  have hAP := polylog_of_tight hA
  have hWord := word_rate model hFast A w r L hL hr hA hw
  have hReference : Bound (fun x => GeneralPaperStoredReferenceReadWork.readBound model (A x) (A x)) r L :=
    rate_mono (GeneralPaperStoredReadWorkRates.reference_rate model hFast A L hL hA) hr
  unfold GeneralPaperStoredDenominatorWork.bound
  fun_prop

end Blotto.GeneralPaperStoredBooleanWorkRates
