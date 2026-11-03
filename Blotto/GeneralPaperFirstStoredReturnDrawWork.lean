import Blotto.GeneralPaperFirstStoredCommonDrawWork

/-! Every corrected selected constructor return has complete common-runtime
expected work. The grouped proof uses the actual cache and its own midpoint
index directly; no source-precision transport changes the executed draw. -/
namespace Blotto.GeneralPaperFirstStoredReturnDrawWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (A n k b : ℕ) : ℕ :=
  GeneralPaperStoredCommonWork.dominantBound model A n b+
    GeneralPaperFirstStoredCommonDrawWork.groupedBound model (A-1) n k b

theorem expected_work {n : ℕ} (model : RationalCostModel) (W S k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ)
    (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (returned : Installed a.address) (hReturn : (GeneralPaperStoredSelectedConstruction.run model S a).1 = some returned) :
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model a.address returned a.branch trace).work : ℝ≥0∞)
      ∂(GeneralPaperEqualBitBranchDraw.traceLaw a.branch : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
      (bound model a.address n k (rationalWordWidth budget) : ℝ≥0∞) := by
  rcases a with ⟨branch,A,hAddress⟩
  cases branch with
  | dominant chosen heavy row correct =>
    let a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget :=
      ⟨.dominant chosen heavy row correct,A,hAddress⟩
    have hReturned : (GeneralPaperStoredDominantOuterConstruction.run model S A chosen.val row).values = some returned := by
      simpa only [GeneralPaperStoredSelectedConstruction.run] using hReturn
    have hPoint := GeneralPaperFirstStoredCommonDrawWork.dominant_work model W S k values v hv budget a chosen heavy row correct rfl returned hReturned
      0 (fun _ => []) GeneralPaperBooleanFreshWord.nextList []
    change (GeneralPaperStoredSelectedDraw.run model A returned 0 (fun _ => []) GeneralPaperBooleanFreshWord.nextList []).work ≤
      GeneralPaperStoredCommonWork.dominantBound model A n (rationalWordWidth budget) at hPoint
    let pBranch : GeneralPaperEqualBitBranch.Prepared (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget :=
      .dominant chosen heavy row correct
    have hMean : (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model A returned pBranch trace).work : ℝ≥0∞)
        ∂(GeneralPaperEqualBitBranchDraw.traceLaw pBranch :
          Measure (GeneralPaperEqualBitBranchDraw.Trace pBranch))) ≤
        (GeneralPaperStoredCommonWork.dominantBound model A n (rationalWordWidth budget) : ℝ≥0∞) := by
      calc
        _ ≤ ∫⁻ _trace, (GeneralPaperStoredCommonWork.dominantBound model A n (rationalWordWidth budget) : ℝ≥0∞)
            ∂(GeneralPaperEqualBitBranchDraw.traceLaw pBranch :
              Measure (GeneralPaperEqualBitBranchDraw.Trace pBranch)) := by
          apply lintegral_mono
          intro trace
          change ((GeneralPaperStoredSelectedDraw.run model A returned 0 (fun _ => []) GeneralPaperBooleanFreshWord.nextList []).work : ℝ≥0∞) ≤
            (GeneralPaperStoredCommonWork.dominantBound model A n (rationalWordWidth budget) : ℝ≥0∞)
          exact_mod_cast hPoint
        _ = _ := by simp only [lintegral_const,measure_univ,mul_one]
    exact hMean.trans (by exact_mod_cast (show GeneralPaperStoredCommonWork.dominantBound model A n (rationalWordWidth budget) ≤
      bound model A n k (rationalWordWidth budget) by unfold bound; omega))
  | grouped small sampler hK hB =>
    change A=sampler.address+1 at hAddress
    subst A
    have hReturned : (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).values=some returned := by
      have hData := hReturn
      simp only [GeneralPaperStoredSelectedConstruction.run,GeneralPaperStoredSelectedReturnWork.recast_self] at hData
      obtain ⟨actual,hActual,hSame⟩ := Option.map_eq_some_iff.mp hData
      exact hActual.trans (congrArg some hSame)
    have hMean := GeneralPaperFirstStoredCommonDrawWork.grouped_expected model W S k values v hv small budget sampler hK hB returned hReturned
    change (∫⁻ trace,((GeneralPaperStoredCommonWork.observed model (sampler.address+1) returned
        sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(GeneralPaperEqualRejectionTraceMeasure.law sampler.prepared.D sampler.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
          Measure (GeneralPaperEqualRejectionTraceMeasure.Trace sampler.prepared.D sampler.prepared.midpointBits))) ≤ _
    apply hMean.trans
    have hNat : GeneralPaperFirstStoredCommonDrawWork.groupedBound model sampler.address n k (rationalWordWidth budget) ≤
        bound model (sampler.address+1) n k (rationalWordWidth budget) := by
      unfold bound
      rw [show sampler.address+1-1=sampler.address by omega]
      omega
    exact_mod_cast hNat

end Blotto.GeneralPaperFirstStoredReturnDrawWork
