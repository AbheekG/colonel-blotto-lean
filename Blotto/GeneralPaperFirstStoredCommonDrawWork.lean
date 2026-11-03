import Blotto.GeneralPaperFirstStoredAllocationBound

/-! Complete marker-selected stored drawing for the corrected source.
Rejection and the one postselection/output pass are charged in the same
mixed-width installed memory, with capacities derived from actual fields. -/
namespace Blotto.GeneralPaperFirstStoredCommonDrawWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def outerBound (model : RationalCostModel) (I n k b : ℕ) : ℕ :=
  GeneralPaperStoredDispatchLoadWork.groupedBound model (I+1)+
    GeneralPaperFirstStoredAllocationBound.nativeBound model I n k b+256*(I+1)

def groupedBound (model : RationalCostModel) (I n k b : ℕ) : ℕ :=
  GeneralPaperStoredOuterReadWork.markerBound model (I+1)+outerBound model I n k b+64*(I+2)

theorem capacities {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (small : ∀ j,2*(rounded true model W k values v hv).weight j≤1) (budget : ℚ)
    (a : GeneralPaperEqualStoredBitSampler.Sampler (terminal (rounded true model W k values v hv) small).partition
      (lottery (rounded true model W k values v hv) small)) (hk : a.exponent=k) (hB : a.prepared.budget=budget) :
    (GeneralPaperEqualMeasuredRetainedPlan.sampler model S a.address a).sizes.sum<2^a.address ∧
    (GeneralPaperEqualMeasuredRetainedPlan.sampler model S a.address a).sizes.sum+
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (a.address+1)).sizes.sum<2^(a.address+1) := by
  let selected : GeneralPaperEqualSelectedSampler.Sampler (rounded true model W k values v hv) k budget :=
    ⟨.grouped small a hk hB,a.address+1,rfl⟩
  exact ⟨GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget selected,
    GeneralPaperEqualFirstMeasuredLayout.total_capacity model W S k values v hv budget selected⟩

theorem outer_expected {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (small : ∀ j,2*(rounded true model W k values v hv).weight j≤1) (budget : ℚ)
    (a : GeneralPaperEqualStoredBitSampler.Sampler (terminal (rounded true model W k values v hv) small).partition
      (lottery (rounded true model W k values v hv) small)) (hk : a.exponent=k) (hB : a.prepared.budget=budget)
    (returned : Installed (a.address+1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S a).values=some returned) :
    (∫⁻ trace,((GeneralPaperStoredGroupedOuterLaw.observed model (a.address+1) returned
        a.prepared.D a.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law a.prepared.D a.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive a.prepared) :
        Measure (Trace a.prepared.D a.prepared.midpointBits))) ≤
      (outerBound model a.address n k (rationalWordWidth budget) : ℝ≥0∞) := by
  obtain ⟨hInner,hOuter⟩ := capacities model W S k values v hv small budget a hk hB
  have hs : 2 ≤ GeneralPaperEqualNativeSampler.segmentHeight n (k+1) := by
    unfold GeneralPaperEqualNativeSampler.segmentHeight GeneralPaperEqualNativeSampler.fieldHeight expressionHeightBudget
    omega
  have hBudget : RationalHeight a.prepared.budget (rationalWordWidth budget) := by
    rw [hB]
    exact rationalHeight_of_wordWidth budget
  have hExpected := GeneralPaperStoredGroupedOuterWork.every_returned_expected model S
    (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) (rationalWordWidth budget) (binaryWordWidth n+k+10)
    a hInner hOuter hs (GeneralPaperEqualFirstHeights.lottery_height true model W k values v hv small) hBudget
    (by omega) (GeneralPaperEqualFirstHeights.route_height true model W k values v hv small a.prepared) returned hReturn
  have hCompare := GeneralPaperFirstStoredAllocationBound.allocation_bound model W k (rationalWordWidth budget)
    values v hv small a hk
  have hTotal : GeneralPaperStoredGroupedOuterWork.bound model (GeneralPaperEqualNativeSampler.segmentHeight n (k+1))
      (rationalWordWidth budget) (binaryWordWidth n+k+10) a ≤ outerBound model a.address n k (rationalWordWidth budget) := by
    unfold GeneralPaperStoredGroupedOuterWork.bound outerBound
    omega
  exact hExpected.trans (by exact_mod_cast hTotal)

theorem grouped_expected {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (small : ∀ j,2*(rounded true model W k values v hv).weight j≤1) (budget : ℚ)
    (a : GeneralPaperEqualStoredBitSampler.Sampler (terminal (rounded true model W k values v hv) small).partition
      (lottery (rounded true model W k values v hv) small)) (hk : a.exponent=k) (hB : a.prepared.budget=budget)
    (returned : Installed (a.address+1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S a).values=some returned) :
    (∫⁻ trace,((GeneralPaperStoredCommonWork.observed model (a.address+1) returned
        a.prepared.D a.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law a.prepared.D a.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive a.prepared) :
        Measure (Trace a.prepared.D a.prepared.midpointBits))) ≤
      (groupedBound model a.address n k (rationalWordWidth budget) : ℝ≥0∞) := by
  exact GeneralPaperStoredCommonWork.grouped_expected model S _ a
    (capacities model W S k values v hv small budget a hk hB).2 returned hReturn
    (outer_expected model W S k values v hv small budget a hk hB returned hReturn)

theorem dominant_vertex {n : ℕ} (model : RationalCostModel) (W S k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ)
    (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv).weight chosen)
    (row : RationalResourceArray n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy row correct) (returned : Installed a.address)
    (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).values = some returned) :
    (GeneralPaperStoredDominantOuterDraw.run model a.address returned).work ≤ GeneralPaperStoredDominantOuterWork.vertexBound model a.address n (rationalWordWidth budget) := by
  obtain ⟨hA,hInner,hOuter⟩ := GeneralPaperFirstStoredDominantContract.bounds model W S k values v hv budget a chosen heavy row correct hBranch
  have hWork := GeneralPaperStoredDominantOuterWork.every_returned_work model S a.address chosen.val row hA hInner hOuter returned hReturn
  have hVertex := GeneralPaperStoredDominantEmissionWork.vertex_bound model a.address budget chosen row correct
  unfold GeneralPaperStoredDominantOuterWork.bound at hWork
  unfold GeneralPaperStoredDominantOuterWork.vertexBound
  omega

theorem dominant_work {n : ℕ} {R : Type*} (model : RationalCostModel) (W S k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ)
    (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv).weight chosen)
    (row : RationalResourceArray n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy row correct) (returned : Installed a.address)
    (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).values = some returned)
    (cap : ℕ) (tape : ℕ → List Bool) (next : R → Bool × R) (state : R) :
    (GeneralPaperStoredSelectedDraw.run model a.address returned cap tape next state).work ≤
      GeneralPaperStoredCommonWork.dominantBound model a.address n (rationalWordWidth budget) := by
  obtain ⟨hA,_,hOuter⟩ := GeneralPaperFirstStoredDominantContract.bounds model W S k values v hv budget a chosen heavy row correct hBranch
  have hMarker := GeneralPaperStoredOuterMarker.dominant_return model S a.address chosen.val row hA hOuter returned hReturn
  have hMarkerWork := GeneralPaperStoredReturnedMarkerWork.dominant model S a.address chosen.val row hA hOuter returned hReturn
  have hDraw := dominant_vertex model W S k values v hv budget a chosen heavy row correct hBranch returned hReturn
  rw [(GeneralPaperStoredSelectedDraw.dominant model a.address returned cap tape next state hMarker).2.2.2]
  unfold GeneralPaperStoredCommonWork.dominantBound
  omega


end Blotto.GeneralPaperFirstStoredCommonDrawWork
