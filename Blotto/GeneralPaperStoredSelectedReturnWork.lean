import Blotto.GeneralPaperStoredCommonInputWork

/-! Every selected source constructor return has the complete actual
common-runtime expected-work bound. Existing cache uniqueness identifies
all valid grouped returns with the native cache, including copied data. -/
namespace Blotto.GeneralPaperStoredSelectedReturnWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualInputDomain (Input)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (A n k b : ℕ) : ℕ :=
  GeneralPaperStoredCommonWork.dominantBound model A n b + GeneralPaperStoredCommonWork.nativeGroupedBound model (A - 1) n k b

theorem recast_self (A : ℕ) (h : A = A) :
    GeneralPaperStoredSelectedConstruction.recast h = (fun value : Installed A => value) := by
  cases h
  rfl

theorem grouped_canonical {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler
      (GeneralPaperEqualFiniteKernel.terminal (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) small).partition
      (GeneralPaperEqualFiniteKernel.lottery (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) small))
    (hK : sampler.exponent = k) (hB : sampler.prepared.budget = budget) :
    sampler = GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget :=
  GeneralPaperEqualBitCanonical.sampler_canonical sampler k budget hK hB

theorem expected_work {n : ℕ} (model : RationalCostModel) (W S k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ)
    (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (returned : Installed a.address) (hReturn : (GeneralPaperStoredSelectedConstruction.run model S a).1 = some returned) :
    (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model a.address returned a.branch trace).work : ℝ≥0∞)
      ∂(GeneralPaperEqualBitBranchDraw.traceLaw a.branch : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
      (bound model a.address n k (rationalWordWidth budget) : ℝ≥0∞) := by
  rcases a with ⟨branch,A,hAddress⟩
  cases branch with
  | dominant chosen heavy row correct =>
    let a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget :=
      ⟨.dominant chosen heavy row correct,A,hAddress⟩
    have hReturned : (GeneralPaperStoredDominantOuterConstruction.run model S A chosen.val row).values = some returned := by
      simpa only [GeneralPaperStoredSelectedConstruction.run] using hReturn
    have hPoint := GeneralPaperStoredCommonWork.dominant_native_work model W S k values v hv budget a chosen heavy row correct rfl returned hReturned
      0 (fun _ => []) GeneralPaperBooleanFreshWord.nextList []
    change (GeneralPaperStoredSelectedDraw.run model A returned 0 (fun _ => []) GeneralPaperBooleanFreshWord.nextList []).work ≤
      GeneralPaperStoredCommonWork.dominantBound model A n (rationalWordWidth budget) at hPoint
    let pBranch : GeneralPaperEqualBitBranch.Prepared (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget :=
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
    change A = sampler.address + 1 at hAddress
    subst A
    have hCanonical := grouped_canonical model W k values v hv small budget sampler hK hB
    cases hCanonical
    let source := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
    have hReturned : (GeneralPaperStoredGroupedOuterConstruction.run model S source).values = some returned := by
      have hData := hReturn
      simp only [GeneralPaperStoredSelectedConstruction.run,recast_self] at hData
      obtain ⟨actual,hActual,hSame⟩ := Option.map_eq_some_iff.mp hData
      exact hActual.trans (congrArg some hSame)
    have hMean := GeneralPaperStoredCommonWork.native_grouped_expected model W S k values v hv small budget returned hReturned
    change (∫⁻ trace, ((GeneralPaperStoredCommonWork.observed model (source.address + 1) returned source.prepared.D source.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(GeneralPaperEqualRejectionTraceMeasure.law source.prepared.D source.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive source.prepared) :
          Measure (GeneralPaperEqualRejectionTraceMeasure.Trace source.prepared.D source.prepared.midpointBits))) ≤ _
    apply hMean.trans
    have hPred : source.address + 1 - 1 = source.address := by omega
    have hNat : GeneralPaperStoredCommonWork.nativeGroupedBound model source.address n k (rationalWordWidth budget) ≤
        bound model (source.address + 1) n k (rationalWordWidth budget) := by
      unfold bound
      rw [hPred]
      omega
    exact_mod_cast hNat

def inputScale {model : RationalCostModel} (p : Input model) : ℕ :=
  (p.n + 1) * GeneralPaperEqualBitDrawRates.size p.n p.k (rationalWordWidth p.budget)

theorem input_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (A K : ℕ) :
    Bound (fun p : Input model => bound model (GeneralPaperStoredSelectedPipeline.width model A K p) p.n p.k (rationalWordWidth p.budget))
      inputScale GeneralPaperStoredNativeReadRates.drawLog := by
  have hA := GeneralPaperStoredNativeReadRates.address_tight model A K
  have hInner : Tight (fun p : Input model => GeneralPaperStoredSelectedPipeline.width model A K p - 1) GeneralPaperStoredNativeReadRates.drawLog := by
    obtain ⟨C,hC⟩ := hA
    exact ⟨C,fun p => (Nat.sub_le _ _).trans (hC p)⟩
  have hScale : ∀ p : Input model,GeneralPaperStoredNativeReadRates.scale p ≤ inputScale p := by
    intro p
    have hPositive := GeneralPaperEqualBitDrawRates.size_positive p.n p.k (rationalWordWidth p.budget)
    have hN := Nat.mul_le_mul_left p.n hPositive
    unfold GeneralPaperStoredNativeReadRates.scale inputScale GeneralPaperEqualBitDrawRates.size at *
    nlinarith only [hN]
  have hDominant := rate_mono (GeneralPaperStoredCommonInputWork.dominant_rate model hFast A K) hScale
  have hGrouped := GeneralPaperStoredCommonWork.native_grouped_rate model hFast _ (fun p : Input model => p.n)
    (fun p => p.k) (fun p => rationalWordWidth p.budget) hInner
  unfold bound
  exact bound_add _ _ inputScale GeneralPaperStoredNativeReadRates.drawLog GeneralPaperStoredNativeReadRates.log_positive hDominant hGrouped

end Blotto.GeneralPaperStoredSelectedReturnWork
