import Blotto.GeneralPaperStoredReturnedMarkerWork

/-! Complete common runtime work includes its actual marker read and the
selected actual outer draw. Native grouped expected-work rates and dominant
vertex prices retain all executed dispatch work. -/
namespace Blotto.GeneralPaperStoredCommonWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualRejectionTraceMeasure
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

noncomputable def observed (model : RationalCostModel) (A : ℕ) (outer : Installed A) (N K : ℕ) (trace : Trace N K) :=
  GeneralPaperStoredSelectedDraw.run model A outer (trace.1 + 1)
    (GeneralPaperStoredRejectionTrace.rawBlocks N (GeneralPaperEqualBooleanTraceCost.tapeFor N K trace))
    GeneralPaperBooleanFreshWord.nextList (List.ofFn (scalar N K trace.1 trace.2))

def nativeGroupedBound (model : RationalCostModel) (I n k b : ℕ) : ℕ :=
  GeneralPaperStoredOuterReadWork.markerBound model (I + 1) + GeneralPaperStoredGroupedOuterNativeWork.bound model I n k b + 64 * (I + 2)

def dominantBound (model : RationalCostModel) (A n b : ℕ) : ℕ :=
  GeneralPaperStoredOuterReadWork.markerBound model A + GeneralPaperStoredDominantOuterWork.vertexBound model A n b + 64 * (A + 1)

theorem observed_grouped {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (small : ∀ j,2 * v.weight j ≤ 1)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler (GeneralPaperEqualFiniteKernel.terminal v small).partition
      (GeneralPaperEqualFiniteKernel.lottery v small)) (hK : sampler.exponent = k) (hB : sampler.prepared.budget = budget)
    (trace : Trace sampler.prepared.D sampler.prepared.midpointBits) :
    observed model A outer sampler.prepared.D sampler.prepared.midpointBits trace =
      GeneralPaperStoredSelectedLaw.observed model A outer (.grouped small sampler hK hB) trace := rfl

theorem grouped_expected {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S B : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (sampler.address + 1)).sizes.sum < 2 ^ (sampler.address + 1))
    (returned : Installed (sampler.address + 1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).values = some returned)
    (hExpected : (∫⁻ trace, ((GeneralPaperStoredGroupedOuterLaw.observed model (sampler.address + 1) returned sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D sampler.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
        Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) ≤ (B : ℝ≥0∞)) :
    (∫⁻ trace, ((observed model (sampler.address + 1) returned sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D sampler.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
        Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) ≤
      (GeneralPaperStoredOuterReadWork.markerBound model (sampler.address + 1) + B + 64 * (sampler.address + 2) : ℕ) := by
  have hMarker := GeneralPaperStoredOuterMarker.grouped_return model S sampler hCap returned hReturn
  have hMarkerWork := GeneralPaperStoredReturnedMarkerWork.grouped model S sampler hCap returned hReturn
  let C := GeneralPaperStoredOuterReadWork.markerBound model (sampler.address + 1) + 64 * (sampler.address + 2)
  have hPoint (trace : Trace sampler.prepared.D sampler.prepared.midpointBits) :
      (observed model (sampler.address + 1) returned sampler.prepared.D sampler.prepared.midpointBits trace).work ≤
        (GeneralPaperStoredGroupedOuterLaw.observed model (sampler.address + 1) returned sampler.prepared.D sampler.prepared.midpointBits trace).work + C := by
    unfold observed GeneralPaperStoredGroupedOuterLaw.observed
    rw [(GeneralPaperStoredSelectedDraw.grouped model (sampler.address + 1) returned (trace.1 + 1) _
      GeneralPaperBooleanFreshWord.nextList _ hMarker).2.2.2]
    unfold C
    omega
  calc
    _ ≤ ∫⁻ trace, (((GeneralPaperStoredGroupedOuterLaw.observed model (sampler.address + 1) returned sampler.prepared.D sampler.prepared.midpointBits trace).work + C : ℕ) : ℝ≥0∞)
        ∂(law sampler.prepared.D sampler.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
          Measure (Trace sampler.prepared.D sampler.prepared.midpointBits)) :=
      lintegral_mono (fun trace => (show ((observed model (sampler.address + 1) returned sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞) ≤
        (((GeneralPaperStoredGroupedOuterLaw.observed model (sampler.address + 1) returned sampler.prepared.D sampler.prepared.midpointBits trace).work + C : ℕ) : ℝ≥0∞) by exact_mod_cast hPoint trace))
    _ = (∫⁻ trace, ((GeneralPaperStoredGroupedOuterLaw.observed model (sampler.address + 1) returned sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞)
        ∂(law sampler.prepared.D sampler.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
          Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) + C := by
      simp only [Nat.cast_add]
      rw [lintegral_add_left (measurable_of_countable _)]
      simp only [lintegral_const,measure_univ,mul_one]
    _ ≤ (B : ℝ≥0∞) + C := add_le_add hExpected le_rfl
    _ = _ := by simp only [C,Nat.cast_add]; ac_rfl

theorem native_grouped_expected {n : ℕ} (model : RationalCostModel) (W S k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (returned : Installed ((GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget).address + 1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S
      (GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget)).values = some returned) :
    let source := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
    (∫⁻ trace, ((observed model (source.address + 1) returned source.prepared.D source.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law source.prepared.D source.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive source.prepared) :
        Measure (Trace source.prepared.D source.prepared.midpointBits))) ≤
      (nativeGroupedBound model source.address n k (rationalWordWidth budget) : ℝ≥0∞) := by
  dsimp only
  have hExpected := GeneralPaperStoredGroupedOuterNativeWork.native_expected model W S k values v hv small budget returned hReturn
  exact grouped_expected model S _ _ (GeneralPaperStoredGroupedOuterNative.bounds model W S k values v hv small budget).2 returned hReturn hExpected

theorem dominant_native_work {n : ℕ} {R : Type*} (model : RationalCostModel) (W S k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ)
    (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight chosen)
    (row : RationalResourceArray n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy row correct) (returned : Installed a.address)
    (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).values = some returned)
    (cap : ℕ) (tape : ℕ → List Bool) (next : R → Bool × R) (state : R) :
    (GeneralPaperStoredSelectedDraw.run model a.address returned cap tape next state).work ≤
      dominantBound model a.address n (rationalWordWidth budget) := by
  obtain ⟨hA,_,hOuter⟩ := GeneralPaperStoredDominantOuterContract.bounds model W S k values v hv budget a chosen heavy row correct hBranch
  have hMarker := GeneralPaperStoredOuterMarker.dominant_return model S a.address chosen.val row hA hOuter returned hReturn
  have hMarkerWork := GeneralPaperStoredReturnedMarkerWork.dominant model S a.address chosen.val row hA hOuter returned hReturn
  have hDraw := GeneralPaperStoredDominantOuterWork.native_vertex model W S k values v hv budget a chosen heavy row correct hBranch returned hReturn
  rw [(GeneralPaperStoredSelectedDraw.dominant model a.address returned cap tape next state hMarker).2.2.2]
  unfold dominantBound
  omega

theorem native_grouped_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (I n k b : α → ℕ) (hI : Tight I (fun x => GeneralPaperEqualBitDrawRates.log (n x) (k x) (b x))) :
    Bound (fun x => nativeGroupedBound model (I x) (n x) (k x) (b x))
      (fun x => (n x + 1) * GeneralPaperEqualBitDrawRates.size (n x) (k x) (b x))
      (fun x => GeneralPaperEqualBitDrawRates.log (n x) (k x) (b x)) := by
  let L := fun x => GeneralPaperEqualBitDrawRates.log (n x) (k x) (b x)
  let r := fun x => (n x + 1) * GeneralPaperEqualBitDrawRates.size (n x) (k x) (b x)
  have hL : ∀ x,1 ≤ L x := by intro x; unfold L GeneralPaperEqualBitDrawRates.log; omega
  have hr : ∀ x,1 ≤ r x := fun x => (GeneralPaperEqualBitDrawRates.size_positive (n x) (k x) (b x)).trans
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (GeneralPaperEqualBitDrawRates.size (n x) (k x) (b x)) (by omega : 1 ≤ n x + 1))
  have hIPlus : Tight (fun x => I x + 1) L := by fun_prop
  have hIBase : Polylog I L := polylog_of_tight hI
  have hIP := polylog_of_tight hIPlus
  have hMarker := rate_mono (GeneralPaperStoredOuterWorkRates.marker_rate model hFast _ L hL hIPlus) hr
  have hOuter := GeneralPaperStoredGroupedOuterNativeWork.native_rate model hFast I n k b hI
  unfold nativeGroupedBound
  fun_prop

theorem dominant_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A n b r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hA : Tight A L) (hn : Bound n r L) (hb : Bound b r L) :
    Bound (fun x => dominantBound model (A x) (n x) (b x)) r L := by
  have hAP := polylog_of_tight hA
  have hMarker := rate_mono (GeneralPaperStoredOuterWorkRates.marker_rate model hFast A L hL hA) hr
  have hOuter := GeneralPaperStoredDominantOuterWork.vertex_rate model hFast A n b r L hL hr hA hn hb
  unfold dominantBound
  fun_prop

end Blotto.GeneralPaperStoredCommonWork
