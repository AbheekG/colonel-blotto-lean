import Blotto.GeneralPaperEqualPureCopyRates

/-! Actual initialized preparation plus all retained copies has the sharp
paper time rate and preserves the same complete selected sampler contract.
Copy lifetime/layout joins remain separate obligations. -/
namespace Blotto.GeneralPaperEqualCopiedContract
open MeasureTheory
open GeneralPaperEqualInputDomain GeneralPaperEqualInputHeadline
open GeneralPaperEqualSelectedSampler (traceLaw observed outputLaw realDecode)
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

theorem paper_time_and_returned_draw (model : RationalCostModel)
    (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ At et : ℕ, ∀ p : Input model,
      let result := GeneralPaperEqualCopiedPipeline.run model (word K p) K p
      let a := result.1
      result.2 ≤ At * inputSize p * (paperLog p) ^ et ∧
      GeneralPaperEqualSelectedDescription.footprint a ≤
        2 * GeneralPaperEqualDescriptionRates.paperBound p.n p.k (rationalWordWidth p.budget) ∧
      GeneralPaperEqualSelectedDescription.footprint a < 2 ^ a.address ∧
      (∫⁻ trace, ((observed model a trace).work : ℝ≥0∞) ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
        (GeneralPaperEqualSelectedDraw.workBound model p.n p.k (rationalWordWidth p.budget) : ℝ≥0∞) ∧
      (∫⁻ trace, ((observed model a trace).reads : ℝ≥0∞) ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
        (GeneralPaperEqualSelectedDraw.readsBound p.n p.k : ℝ≥0∞) ∧
      (traceLaw a).map (realDecode model a) = outputLaw model a ∧
      (∀ᵐ trace ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch)),
        ∃ row, (observed model a trace).output = some row) ∧
      (0 ≤ p.budget → ∀ trace row, (observed model a trace).output = some row →
        FullBudget (p.budget : ℝ) row.realAllocation ∧
          ∀ j, RationalHeight (row.allocation j)
            (33554432 * (rationalWordWidth p.budget + binaryWordWidth p.n + p.k + 10))) ∧
      (epsilon p < 1 → 0 < p.budget →
        Supported (p.budget : ℝ) (outputLaw model a) ∧
        regret p.selector.values (p.budget : ℝ) (outputLaw model a) (outputLaw model a) ≤ (epsilon p : ℝ)) := by
  obtain ⟨At,et,ht⟩ := GeneralPaperEqualCopiedPipeline.paper_time model hFast K
  refine ⟨At,et,fun p => ?_⟩
  dsimp only
  refine ⟨ht p,
    GeneralPaperEqualSelectedDescription.paper_bound model _ p.k p.values p.selector p.correct p.budget _,
    GeneralPaperEqualSelectedDescription.capacity model _ p.k p.values p.selector p.correct p.budget _,
    GeneralPaperEqualSelectedDraw.expected_work model _ p.k p.values p.selector p.correct p.budget _,
    GeneralPaperEqualSelectedDraw.expected_reads model _ p.k p.values p.selector p.correct p.budget _,
    GeneralPaperEqualSelectedSampler.law model _, GeneralPaperEqualSelectedSampler.completed_ae model _,
    fun hB trace row h => GeneralPaperEqualSelectedDraw.written_output model _ p.k p.values p.selector p.correct p.budget
      hB (rationalHeight_of_wordWidth p.budget) _ trace row h,
    fun hOne hB => GeneralPaperEqualCopiedPipeline.epsilon model _ K p hOne hB⟩

end Blotto.GeneralPaperEqualCopiedContract
