import Blotto.GeneralPaperStoredGroupedOuterWork
import Blotto.GeneralPaperStoredNativeAllocationBound

/-! Native actual mixed-width constructor returns derive both capacities
and complete expected draw work. The corresponding native paper-input rate
uses that same majorant and its actual inner/outer representation widths. -/
namespace Blotto.GeneralPaperStoredGroupedOuterNativeWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualRejectionTraceMeasure
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (I n k b : ℕ) : ℕ :=
  GeneralPaperStoredDispatchLoadWork.groupedBound model (I + 1) +
    GeneralPaperStoredDrawMajorant.nativeBound model I n k b + 256 * (I + 1)

theorem native_expected {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (returned : Installed ((GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget).address + 1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S
      (GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget)).values = some returned) :
    let source := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
    (∫⁻ trace, ((GeneralPaperStoredGroupedOuterLaw.observed model (source.address + 1) returned source.prepared.D source.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law source.prepared.D source.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive source.prepared) :
        Measure (Trace source.prepared.D source.prepared.midpointBits))) ≤
      (bound model source.address n k (rationalWordWidth budget) : ℝ≥0∞) := by
  dsimp only
  let source := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
  obtain ⟨hInner,hOuter⟩ := GeneralPaperStoredGroupedOuterNative.bounds model W S k values v hv small budget
  have hs : 2 ≤ GeneralPaperEqualNativeSampler.segmentHeight n k := by
    unfold GeneralPaperEqualNativeSampler.segmentHeight GeneralPaperEqualNativeSampler.fieldHeight expressionHeightBudget
    omega
  have hExpected := GeneralPaperStoredGroupedOuterWork.every_returned_expected model S (GeneralPaperEqualNativeSampler.segmentHeight n k)
    (rationalWordWidth budget) (binaryWordWidth n + k + 9) source hInner hOuter hs
    (GeneralPaperEqualNativeSampler.native_lottery_height true model W k values v hv small) (rationalHeight_of_wordWidth budget)
    (by omega) (GeneralPaperEqualNativeCache.route_height true model W k values v hv small budget) returned hReturn
  have hCompare := GeneralPaperStoredNativeAllocationBound.native_bound true model W k values v hv small budget
  change GeneralPaperStoredAllocationWork.expectedBound model source.address (GeneralPaperEqualNativeSampler.segmentHeight n k)
    (rationalWordWidth budget) (binaryWordWidth n + k + 9) source ≤
    GeneralPaperStoredDrawMajorant.nativeBound model source.address n k (rationalWordWidth budget) at hCompare
  have hTotal : GeneralPaperStoredGroupedOuterWork.bound model (GeneralPaperEqualNativeSampler.segmentHeight n k)
      (rationalWordWidth budget) (binaryWordWidth n + k + 9) source ≤ bound model source.address n k (rationalWordWidth budget) := by
    unfold GeneralPaperStoredGroupedOuterWork.bound bound
    omega
  exact hExpected.trans (by exact_mod_cast hTotal)

theorem native_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (I n k b : α → ℕ) (hI : Tight I (fun x => GeneralPaperEqualBitDrawRates.log (n x) (k x) (b x))) :
    Bound (fun x => bound model (I x) (n x) (k x) (b x))
      (fun x => (n x + 1) * GeneralPaperEqualBitDrawRates.size (n x) (k x) (b x))
      (fun x => GeneralPaperEqualBitDrawRates.log (n x) (k x) (b x)) := by
  let L := fun x => GeneralPaperEqualBitDrawRates.log (n x) (k x) (b x)
  let r := fun x => (n x + 1) * GeneralPaperEqualBitDrawRates.size (n x) (k x) (b x)
  have hL : ∀ x,1 ≤ L x := by intro x; unfold L GeneralPaperEqualBitDrawRates.log; omega
  have hr : ∀ x,1 ≤ r x := fun x => (GeneralPaperEqualBitDrawRates.size_positive (n x) (k x) (b x)).trans
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (GeneralPaperEqualBitDrawRates.size (n x) (k x) (b x)) (by omega : 1 ≤ n x + 1))
  have hIPlus : Tight (fun x => I x + 1) L := by fun_prop
  have hIP := polylog_of_tight hIPlus
  have hMeta : Bound (fun x => GeneralPaperStoredDispatchLoadWork.groupedBound model (I x + 1)) r L :=
    rate_mono (GeneralPaperStoredOuterWorkRates.grouped_rate model hFast _ L hL hIPlus) hr
  have hInner := GeneralPaperStoredNativeDrawRates.native_rate model hFast I n k b hI
  unfold bound
  fun_prop

theorem input_width (model : RationalCostModel) (K : ℕ) :
    Tight (GeneralPaperStoredGroupedInputRates.width model K) (GeneralPaperStoredGroupedInputRates.drawLog (model := model) (K := K)) := by
  refine ⟨2,fun p => ?_⟩
  have hGroups := GeneralPaperEqualNativeCache.group_count
    (GeneralPaperEqualNativeSampler.rounded true model (GeneralPaperEqualInputDomain.word K p.val)
      p.val.k p.val.values p.val.selector p.val.correct) p.property
  change (GeneralPaperStoredGroupedInputRates.source model K p).address ≤ 2 * GeneralPaperStoredGroupedInputRates.drawLog p
  rw [(GeneralPaperStoredGroupedInputRates.source model K p).address_correct]
  exact (GeneralPaperEqualBitDrawRates.metadata_bounds p.val.n _ p.val.k (rationalWordWidth p.val.budget) hGroups).1

theorem input_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : GeneralPaperStoredGroupedInputRates.Grouped model K =>
      bound model (GeneralPaperStoredGroupedInputRates.width model K p) p.val.n p.val.k (rationalWordWidth p.val.budget))
      GeneralPaperStoredGroupedInputRates.scale GeneralPaperStoredGroupedInputRates.drawLog :=
  native_rate model hFast _ _ _ _ (input_width model K)

end Blotto.GeneralPaperStoredGroupedOuterNativeWork
