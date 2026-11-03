import Blotto.GeneralPaperFirstStoredPipelineDrawWork

/-! Sharp complete stored drawing work for the corrected sampler. The
linear precision factor contains original budget words plus the accuracy
index and log dimension; the accuracy input encoding is absent. -/
namespace Blotto.GeneralPaperFirstStoredDrawRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperEqualBitDrawRates (size log)
open GeneralPaperEqualInputDomain (Input)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem native_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A n k b : α → ℕ) (hA : Tight A (fun x => log (n x) (k x+1) (b x))) :
    Bound (fun x => GeneralPaperFirstStoredAllocationBound.nativeBound model (A x) (n x) (k x) (b x))
      (fun x => (n x + 1) * size (n x) (k x+1) (b x)) (fun x => log (n x) (k x+1) (b x)) := by
  let r := fun x => size (n x) ((k x+1)) (b x)
  let L := fun x => log (n x) ((k x+1)) (b x)
  have hL : ∀ x,1 ≤ L x := by intro x; unfold L log; omega
  have hr : ∀ x,1 ≤ r x := fun x => GeneralPaperEqualBitDrawRates.size_positive (n x) ((k x+1)) (b x)
  have hRSmall : Small r L := GeneralPaperStoredNativeDrawRates.size_small n (fun x => k x+1) b
  have hCore : Bound (fun x => binaryWordWidth (n x) + (k x+1) + 10) r L := pointwise _ _ _ 1 (fun x => by unfold r size; omega)
  have hCoreSmall : Small (fun x => binaryWordWidth (n x) + (k x+1) + 10) L := small_mono hRSmall (fun x => by unfold r size; omega)
  have hw : Bound (fun x => GeneralPaperStoredNativeRejectionBound.wordBound (n x) ((k x+1))) r L := by
    unfold GeneralPaperStoredNativeRejectionBound.wordBound
    fun_prop
  have hP : Bound (fun x => 3670016 * GeneralPaperEqualNativeRetainedStorage.short (n x) ((k x+1)) + 3) r L := by
    unfold GeneralPaperEqualNativeRetainedStorage.short
    fun_prop
  have hK : Bound (fun x => k x + 5) r L := pointwise _ _ _ 1 (fun x => by unfold r size; omega)
  have hKs : Small (fun x => k x + 5) L := small_mono hRSmall (fun x => by unfold r size; omega)
  have hSMajor : Bound (fun x => 524288 * (binaryWordWidth (n x) + (k x+1) + 10)) r L := by fun_prop
  have hs : Bound (fun x => GeneralPaperEqualNativeSampler.segmentHeight (n x) ((k x+1))) r L :=
    dominated hSMajor (fun x => GeneralPaperEqualNativeCache.segment_height_bound (n x) ((k x+1)))
  have hSSmallMajor : Small (fun x => 524288 * (binaryWordWidth (n x) + (k x+1) + 10)) L := by fun_prop
  have hss : Small (fun x => GeneralPaperEqualNativeSampler.segmentHeight (n x) ((k x+1))) L :=
    small_mono hSSmallMajor (fun x => GeneralPaperEqualNativeCache.segment_height_bound (n x) ((k x+1)))
  have hb : Bound b r L := pointwise _ _ _ 1 (fun x => by unfold r size; omega)
  have hbs : Small b L := small_mono hRSmall (fun x => by unfold r size; omega)
  have hc : Bound (fun x => binaryWordWidth (n x) + (k x+1) + 9) r L := pointwise _ _ _ 1 (fun x => by unfold r size; omega)
  have hcs : Small (fun x => binaryWordWidth (n x) + (k x+1) + 9) L := small_mono hRSmall (fun x => by unfold r size; omega)
  unfold GeneralPaperFirstStoredAllocationBound.nativeBound
  simpa only [Nat.add_assoc] using GeneralPaperStoredDrawRates.fixed_groups_rate model hFast A n _ _ _ _ b _ r L hL hr hA hw hP hK hKs hs hss hb hbs hc hcs

theorem outer_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (I n k b : α → ℕ) (hI : Tight I (fun x => log (n x) (k x+1) (b x))) :
    Bound (fun x => GeneralPaperFirstStoredCommonDrawWork.outerBound model (I x) (n x) (k x) (b x))
      (fun x => (n x+1)*size (n x) (k x+1) (b x)) (fun x => log (n x) (k x+1) (b x)) := by
  let L := fun x => log (n x) (k x+1) (b x)
  let r := fun x => (n x+1)*size (n x) (k x+1) (b x)
  have hL : ∀ x,1 ≤ L x := by intro x; unfold L log; omega
  have hr : ∀ x,1 ≤ r x := fun x => (GeneralPaperEqualBitDrawRates.size_positive (n x) (k x+1) (b x)).trans
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (size (n x) (k x+1) (b x)) (by omega : 1 ≤ n x+1))
  have hIPlus : Tight (fun x => I x+1) L := by fun_prop
  have hIBase := polylog_of_tight hI
  have hIP := polylog_of_tight hIPlus
  have hMeta := rate_mono (GeneralPaperStoredOuterWorkRates.grouped_rate model hFast _ L hL hIPlus) hr
  have hInner := native_rate model hFast I n k b hI
  unfold GeneralPaperFirstStoredCommonDrawWork.outerBound
  fun_prop

theorem grouped_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (I n k b : α → ℕ) (hI : Tight I (fun x => log (n x) (k x+1) (b x))) :
    Bound (fun x => GeneralPaperFirstStoredCommonDrawWork.groupedBound model (I x) (n x) (k x) (b x))
      (fun x => (n x+1)*size (n x) (k x+1) (b x)) (fun x => log (n x) (k x+1) (b x)) := by
  let L := fun x => log (n x) (k x+1) (b x)
  let r := fun x => (n x+1)*size (n x) (k x+1) (b x)
  have hL : ∀ x,1 ≤ L x := by intro x; unfold L log; omega
  have hr : ∀ x,1 ≤ r x := fun x => (GeneralPaperEqualBitDrawRates.size_positive (n x) (k x+1) (b x)).trans
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (size (n x) (k x+1) (b x)) (by omega : 1 ≤ n x+1))
  have hIPlus : Tight (fun x => I x+1) L := by fun_prop
  have hIBase := polylog_of_tight hI
  have hIP := polylog_of_tight hIPlus
  have hMarker := rate_mono (GeneralPaperStoredOuterWorkRates.marker_rate model hFast _ L hL hIPlus) hr
  have hOuter := outer_rate model hFast I n k b hI
  unfold GeneralPaperFirstStoredCommonDrawWork.groupedBound
  fun_prop

def drawLog {model : RationalCostModel} (p : Input model) : ℕ := log p.n (p.k+1) (rationalWordWidth p.budget)
def inputScale {model : RationalCostModel} (p : Input model) : ℕ := (p.n+1)*size p.n (p.k+1) (rationalWordWidth p.budget)

theorem log_positive {model : RationalCostModel} (p : Input model) : 1 ≤ drawLog p := by unfold drawLog log; omega

theorem address_tight (model : RationalCostModel) (A K : ℕ) :
    Tight (GeneralPaperFirstStoredPipeline.width model A K) (drawLog (model := model)) := by
  refine ⟨3,fun p => ?_⟩
  have h := GeneralPaperEqualSelectedSampler.address_bound (GeneralPaperEqualFirstInputPipeline.run model A K p).1
  have hStep := GeneralPaperEqualFirstBitWork.log_step p.n p.k (rationalWordWidth p.budget)
  have hL := log_positive p
  change (GeneralPaperEqualFirstInputPipeline.run model A K p).1.address ≤ 3*drawLog p
  dsimp only [drawLog] at *
  omega

theorem pipeline_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (A K : ℕ) :
    Bound (GeneralPaperFirstStoredPipelineDrawWork.majorant model A K) inputScale drawLog := by
  have hA := address_tight model A K
  have hInner : Tight (fun p : Input model => GeneralPaperFirstStoredPipeline.width model A K p-1) drawLog := by
    obtain ⟨C,hC⟩ := hA
    exact ⟨C,fun p => (Nat.sub_le _ _).trans (hC p)⟩
  have hr : ∀ p : Input model,1 ≤ inputScale p := by
    intro p
    have h := GeneralPaperEqualBitDrawRates.size_positive p.n (p.k+1) (rationalWordWidth p.budget)
    unfold inputScale
    nlinarith
  have hn : Bound (fun p : Input model => p.n) inputScale drawLog := pointwise _ _ _ 1 (fun p => by
    have h := GeneralPaperEqualBitDrawRates.size_positive p.n (p.k+1) (rationalWordWidth p.budget)
    unfold inputScale
    nlinarith)
  have hb : Bound (fun p : Input model => rationalWordWidth p.budget) inputScale drawLog := pointwise _ _ _ 1 (fun p => by
    unfold inputScale size
    nlinarith)
  have hDominant := GeneralPaperStoredCommonWork.dominant_rate model hFast
    (GeneralPaperFirstStoredPipeline.width model A K) (fun p : Input model => p.n) (fun p => rationalWordWidth p.budget)
    inputScale drawLog log_positive hr hA hn hb
  have hGrouped := grouped_rate model hFast (fun p : Input model => GeneralPaperFirstStoredPipeline.width model A K p-1)
    (fun p => p.n) (fun p => p.k) (fun p => rationalWordWidth p.budget) hInner
  unfold GeneralPaperFirstStoredPipelineDrawWork.majorant GeneralPaperFirstStoredReturnDrawWork.bound
  exact bound_add _ _ inputScale drawLog log_positive hDominant hGrouped

end Blotto.GeneralPaperFirstStoredDrawRates
