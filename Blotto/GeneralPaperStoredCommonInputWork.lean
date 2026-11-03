import Blotto.GeneralPaperStoredCommonWork

/-! Actual paper-input components and growth rates for the common runtime.
The grouped component uses native outer constructor returns. The dominant
component follows the literal branch of copied preparation and its selected
constructor return. No fit or precision premise is supplied by execution. -/
namespace Blotto.GeneralPaperStoredCommonInputWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualInputDomain (Input)
open GeneralPaperUniformResourceGrowth
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def groupedMajorant (model : RationalCostModel) (K : ℕ) (p : GeneralPaperStoredGroupedInputRates.Grouped model K) : ℕ :=
  GeneralPaperStoredCommonWork.nativeGroupedBound model (GeneralPaperStoredGroupedInputRates.width model K p)
    p.val.n p.val.k (rationalWordWidth p.val.budget)

theorem grouped_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (groupedMajorant model K) GeneralPaperStoredGroupedInputRates.scale GeneralPaperStoredGroupedInputRates.drawLog :=
  GeneralPaperStoredCommonWork.native_grouped_rate model hFast _ _ _ _ (GeneralPaperStoredGroupedOuterNativeWork.input_width model K)

theorem grouped_component (model : RationalCostModel) (K S : ℕ) (p : GeneralPaperStoredGroupedInputRates.Grouped model K)
    (returned : Installed (GeneralPaperStoredGroupedInputRates.width model K p + 1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S (GeneralPaperStoredGroupedInputRates.source model K p)).values = some returned) :
    (∫⁻ trace, ((GeneralPaperStoredCommonWork.observed model (GeneralPaperStoredGroupedInputRates.width model K p + 1) returned
      (GeneralPaperStoredGroupedInputRates.source model K p).prepared.D
      (GeneralPaperStoredGroupedInputRates.source model K p).prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law (GeneralPaperStoredGroupedInputRates.source model K p).prepared.D
        (GeneralPaperStoredGroupedInputRates.source model K p).prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive (GeneralPaperStoredGroupedInputRates.source model K p).prepared) :
          Measure (Trace (GeneralPaperStoredGroupedInputRates.source model K p).prepared.D
            (GeneralPaperStoredGroupedInputRates.source model K p).prepared.midpointBits))) ≤ (groupedMajorant model K p : ℝ≥0∞) :=
  GeneralPaperStoredCommonWork.native_grouped_expected model (GeneralPaperEqualInputDomain.word K p.val) S p.val.k
    p.val.values p.val.selector p.val.correct p.property p.val.budget returned hReturn

theorem dominant_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (A K : ℕ) :
    Bound (fun p : Input model => GeneralPaperStoredCommonWork.dominantBound model
      (GeneralPaperStoredSelectedPipeline.width model A K p) p.n (rationalWordWidth p.budget))
      GeneralPaperStoredNativeReadRates.scale GeneralPaperStoredNativeReadRates.drawLog := by
  have hn : Bound (fun p : Input model => p.n) GeneralPaperStoredNativeReadRates.scale GeneralPaperStoredNativeReadRates.drawLog :=
    pointwise _ _ _ 1 (fun p => by unfold GeneralPaperStoredNativeReadRates.scale; omega)
  have hb : Bound (fun p : Input model => rationalWordWidth p.budget) GeneralPaperStoredNativeReadRates.scale GeneralPaperStoredNativeReadRates.drawLog :=
    pointwise _ _ _ 1 (fun p => by unfold GeneralPaperStoredNativeReadRates.scale; omega)
  exact GeneralPaperStoredCommonWork.dominant_rate model hFast _ _ _ _ _ GeneralPaperStoredNativeReadRates.log_positive
    (fun p => by unfold GeneralPaperStoredNativeReadRates.scale; omega) (GeneralPaperStoredNativeReadRates.address_tight model A K) hn hb

theorem dominant_component {model : RationalCostModel} {R : Type*} (A K S : ℕ) (p : Input model)
    (chosen : Fin p.n)
    (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model (GeneralPaperEqualInputDomain.word K p) p.k p.values p.selector p.correct).weight chosen)
    (row : RationalResourceArray p.n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (p.budget : ℝ) chosen)
    (hBranch : (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch = .dominant chosen heavy row correct)
    (returned : Installed (GeneralPaperStoredSelectedPipeline.width model A K p))
    (hReturn : (GeneralPaperStoredSelectedConstruction.run model S (GeneralPaperEqualCopiedPipeline.run model A K p).1).1 = some returned)
    (cap : ℕ) (tape : ℕ → List Bool) (next : R → Bool × R) (state : R) :
    (GeneralPaperStoredSelectedDraw.run model (GeneralPaperStoredSelectedPipeline.width model A K p) returned cap tape next state).work ≤
      GeneralPaperStoredCommonWork.dominantBound model (GeneralPaperStoredSelectedPipeline.width model A K p) p.n (rationalWordWidth p.budget) := by
  have hReturned : (GeneralPaperStoredDominantOuterConstruction.run model S
      (GeneralPaperStoredSelectedPipeline.width model A K p) chosen.val row).values = some returned := by
    unfold GeneralPaperStoredSelectedConstruction.run at hReturn
    split at hReturn
    · rename_i actualChosen actualHeavy actualRow actualCorrect hCase
      have hEq := hBranch.symm.trans hCase
      cases hEq
      exact hReturn
    · rename_i small source hK hB hCase
      cases hBranch.symm.trans hCase
  exact GeneralPaperStoredCommonWork.dominant_native_work model (GeneralPaperEqualInputDomain.word K p) S p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualCopiedPipeline.run model A K p).1 chosen heavy row correct hBranch returned hReturned cap tape next state

end Blotto.GeneralPaperStoredCommonInputWork
