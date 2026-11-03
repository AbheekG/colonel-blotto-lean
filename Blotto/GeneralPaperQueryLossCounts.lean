import Blotto.GeneralPaperCDFPairPlan

/-! Actual cached CDF/tail queries supply the four mesh counts for a primal
or response loss. Integer level updates are computed directly from these
counts; the rational loss expression is reference semantics only.
-/
namespace Blotto.GeneralPaperQueryLossCounts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Plan (k m : ℕ) where
  cdf : GeneralPaperCDFPairPlan.Plan k m
  tails : GeneralPaperSignedTailPlan.Plan k m
  work : ℕ

def prepare {m : ℕ} (k U : ℕ) (cdfSummary tailSummary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (queries : FixedArrayTable m ℕ) : Plan k m :=
  let cdf := GeneralPaperCDFPairPlan.prepare k cdfSummary queries
  let tails := GeneralPaperSignedTailPlan.prepare k U tailSummary queries
  ⟨cdf,tails,cdf.work+tails.work+16⟩

structure Counts where
  lower : ℕ
  upper : ℕ
  positive : ℕ
  negative : ℕ
  work : ℕ

def evaluate {m : ℕ} (k : ℕ)
    (cdfPrefix tailPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (plan : Plan k m) (q : Fin m) : Counts :=
  let cdf := GeneralPaperCDFPairPlan.evaluate k cdfPrefix plan.cdf q
  let tails := GeneralPaperSignedTailPlan.evaluate k tailPrefix plan.tails q
  ⟨cdf.lower,cdf.upper,tails.positive,tails.negative,cdf.work+tails.work+16⟩

def increment (k : ℕ) (response : Bool) (counts : Counts) : ℕ :=
  let N := (GeneralPaperSourceParameters.prepare k).meshDenominator
  if response then GeneralPaperRoundedLosses.responseIncrement N counts.lower counts.upper counts.positive counts.negative
    else GeneralPaperRoundedLosses.primalIncrement N counts.lower counts.upper counts.positive counts.negative

def loss (k : ℕ) (response : Bool) (counts : Counts) : ℚ :=
  let N := (GeneralPaperSourceParameters.prepare k).meshDenominator
  if response then GeneralPaperRoundedLosses.responseLoss N counts.lower counts.upper counts.positive counts.negative
    else GeneralPaperRoundedLosses.primalLoss N counts.lower counts.upper counts.positive counts.negative

def Bounds (k : ℕ) (counts : Counts) : Prop :=
  counts.lower≤(GeneralPaperSourceParameters.prepare k).meshDenominator ∧
  counts.upper≤(GeneralPaperSourceParameters.prepare k).meshDenominator ∧
  counts.positive≤(GeneralPaperSourceParameters.prepare k).meshDenominator ∧
  counts.negative≤(GeneralPaperSourceParameters.prepare k).meshDenominator

theorem evaluate_bounds {m : ℕ} (k U : ℕ)
    (cdfSummary tailSummary cdfValues tailValues : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hCDF : 0<∑ r, cdfValues.read r) (hTail : 0<∑ r, tailValues.read r) (queries : FixedArrayTable m ℕ) (q : Fin m) :
    Bounds k (evaluate k (GeneralPaperEpochPrefixArray.build cdfValues) (GeneralPaperEpochPrefixArray.build tailValues)
      (prepare k U cdfSummary tailSummary queries) q) := by
  have hc := GeneralPaperCDFPairPlan.evaluate_bounds k cdfSummary cdfValues hCDF queries q
  have ht := GeneralPaperSignedTailValues.evaluate_bounds k U tailSummary tailValues hTail queries q
  exact ⟨hc.1,hc.2,ht.1,ht.2⟩

theorem increment_bound (k : ℕ) (response : Bool) (counts : Counts) (h : Bounds k counts) :
    increment k response counts≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  cases response
  · exact GeneralPaperRoundedLosses.primal_increment_bound _ _ _ _ _ h.2.2.1
  · exact GeneralPaperRoundedLosses.response_increment_bound _ _ _ _ _ h.2.2.1

theorem increment_loss (k : ℕ) (response : Bool) (counts : Counts) (h : Bounds k counts) :
    GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment k response counts)=loss k response counts := by
  rw [GeneralPaperSourceParameters.theta_mesh]
  cases response
  · exact GeneralPaperRoundedLosses.primal_increment_loss _ _ _ _ _ (GeneralPaperSourceParameters.mesh_positive k) h.1 h.2.1 h.2.2.2
  · exact GeneralPaperRoundedLosses.response_increment_loss _ _ _ _ _ (GeneralPaperSourceParameters.mesh_positive k) h.1 h.2.1 h.2.2.2

theorem loss_magnitude (k : ℕ) (response : Bool) (counts : Counts) (h : Bounds k counts) : |loss k response counts|≤2 := by
  cases response
  · exact GeneralPaperRoundedLosses.primal_magnitude _ _ _ _ _ (GeneralPaperSourceParameters.mesh_positive k) h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact GeneralPaperRoundedLosses.response_magnitude _ _ _ _ _ (GeneralPaperSourceParameters.mesh_positive k) h.1 h.2.1 h.2.2.1 h.2.2.2

theorem executed_magnitude (k : ℕ) (response : Bool) (counts : Counts) (h : Bounds k counts) :
    |(GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment k response counts):ℝ)|≤2 := by
  rw [increment_loss k response counts h]
  exact_mod_cast loss_magnitude k response counts h

theorem evaluate_work {m : ℕ} (k : ℕ)
    (cdfPrefix tailPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (plan : Plan k m) (q : Fin m) : (evaluate k cdfPrefix tailPrefix plan q).work=48*(30+k)+232 := by
  unfold evaluate
  dsimp only
  rw [GeneralPaperCDFPairPlan.evaluate_work,GeneralPaperSignedTailPlan.evaluate_work]
  omega

theorem prepare_work {m : ℕ} (k U : ℕ) (cdfSummary tailSummary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (queries : FixedArrayTable m ℕ) :
    (prepare k U cdfSummary tailSummary queries).work≤(4*m+2)*((35+k)*(12*(35+k)+34)+120)+192 := by
  have hc := GeneralPaperCDFPairPlan.prepare_work k cdfSummary queries
  have ht := GeneralPaperSignedTailPlan.prepare_work k U tailSummary queries
  change (GeneralPaperCDFPairPlan.prepare k cdfSummary queries).work+
    (GeneralPaperSignedTailPlan.prepare k U tailSummary queries).work+16≤_
  nlinarith

def step {m : ℕ} (k : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (plan : Plan k m) (q : Fin m) : ℕ × ℕ :=
  let counts := evaluate k cdfPrefix tailPrefix plan q
  (increment k response counts,counts.work+24)

theorem step_work {m : ℕ} (k : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (plan : Plan k m) (q : Fin m) : (step k response cdfPrefix tailPrefix plan q).2=48*(30+k)+256 := by
  unfold step
  dsimp only
  rw [evaluate_work]

end Blotto.GeneralPaperQueryLossCounts
