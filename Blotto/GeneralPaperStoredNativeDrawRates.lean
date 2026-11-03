import Blotto.GeneralPaperStoredDrawRates

/-! Complete actual native grouped draw majorants have one output-length
and one additive budget/short-operand precision factor, up to logarithmic
factors. These logarithms omit the original accuracy encoding length. -/
namespace Blotto.GeneralPaperStoredNativeDrawRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperEqualBitDrawRates (size log address)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

theorem size_small {α : Type*} (n k b : α → ℕ) :
    Small (fun x => size (n x) (k x) (b x)) (fun x => log (n x) (k x) (b x)) := by
  refine ⟨1,fun x => ?_⟩
  have hWidth := binaryWordWidth_mono (show size (n x) (k x) (b x) ≤ n x + GeneralPaperEqualBitDrawRates.word (n x) (k x) (b x) + 32 by
    unfold GeneralPaperEqualBitDrawRates.word size
    omega)
  unfold log
  dsimp only
  omega

theorem native_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A n k b : α → ℕ) (hA : Tight A (fun x => log (n x) (k x) (b x))) :
    Bound (fun x => GeneralPaperStoredDrawMajorant.nativeBound model (A x) (n x) (k x) (b x))
      (fun x => (n x + 1) * size (n x) (k x) (b x)) (fun x => log (n x) (k x) (b x)) := by
  let r := fun x => size (n x) (k x) (b x)
  let L := fun x => log (n x) (k x) (b x)
  have hL : ∀ x,1 ≤ L x := by intro x; unfold L log; omega
  have hr : ∀ x,1 ≤ r x := fun x => GeneralPaperEqualBitDrawRates.size_positive (n x) (k x) (b x)
  have hRSmall : Small r L := size_small n k b
  have hCore : Bound (fun x => binaryWordWidth (n x) + k x + 10) r L := pointwise _ _ _ 1 (fun x => by unfold r size; omega)
  have hCoreSmall : Small (fun x => binaryWordWidth (n x) + k x + 10) L := small_mono hRSmall (fun x => by unfold r size; omega)
  have hw : Bound (fun x => GeneralPaperStoredNativeRejectionBound.wordBound (n x) (k x)) r L := by
    unfold GeneralPaperStoredNativeRejectionBound.wordBound
    fun_prop
  have hP : Bound (fun x => 3670016 * GeneralPaperEqualNativeRetainedStorage.short (n x) (k x) + 3) r L := by
    unfold GeneralPaperEqualNativeRetainedStorage.short
    fun_prop
  have hK : Bound (fun x => k x + 5) r L := pointwise _ _ _ 1 (fun x => by unfold r size; omega)
  have hKs : Small (fun x => k x + 5) L := small_mono hRSmall (fun x => by unfold r size; omega)
  have hSMajor : Bound (fun x => 524288 * (binaryWordWidth (n x) + k x + 10)) r L := by fun_prop
  have hs : Bound (fun x => GeneralPaperEqualNativeSampler.segmentHeight (n x) (k x)) r L :=
    dominated hSMajor (fun x => GeneralPaperEqualNativeCache.segment_height_bound (n x) (k x))
  have hSSmallMajor : Small (fun x => 524288 * (binaryWordWidth (n x) + k x + 10)) L := by fun_prop
  have hss : Small (fun x => GeneralPaperEqualNativeSampler.segmentHeight (n x) (k x)) L :=
    small_mono hSSmallMajor (fun x => GeneralPaperEqualNativeCache.segment_height_bound (n x) (k x))
  have hb : Bound b r L := pointwise _ _ _ 1 (fun x => by unfold r size; omega)
  have hbs : Small b L := small_mono hRSmall (fun x => by unfold r size; omega)
  have hc : Bound (fun x => binaryWordWidth (n x) + k x + 9) r L := pointwise _ _ _ 1 (fun x => by unfold r size; omega)
  have hcs : Small (fun x => binaryWordWidth (n x) + k x + 9) L := small_mono hRSmall (fun x => by unfold r size; omega)
  unfold GeneralPaperStoredDrawMajorant.nativeBound
  exact GeneralPaperStoredDrawRates.fixed_groups_rate model hFast A n _ _ _ _ b _ r L hL hr hA hw hP hK hKs hs hss hb hbs hc hcs

theorem address_rate {α : Type*} (n m k b : α → ℕ) (hm : ∀ x,m x ≤ 3) :
    Tight (fun x => address (n x) (m x) (k x) (b x)) (fun x => log (n x) (k x) (b x)) :=
  ⟨2,fun x => (GeneralPaperEqualBitDrawRates.metadata_bounds (n x) (m x) (k x) (b x) (hm x)).1⟩

theorem native_address_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (n m k b : α → ℕ) (hm : ∀ x,m x ≤ 3) :
    Bound (fun x => GeneralPaperStoredDrawMajorant.nativeBound model (address (n x) (m x) (k x) (b x)) (n x) (k x) (b x))
      (fun x => (n x + 1) * size (n x) (k x) (b x)) (fun x => log (n x) (k x) (b x)) :=
  native_rate model hFast _ n k b (address_rate n m k b hm)

end Blotto.GeneralPaperStoredNativeDrawRates
