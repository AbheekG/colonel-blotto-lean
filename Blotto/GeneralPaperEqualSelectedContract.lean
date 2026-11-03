import Blotto.GeneralPaperEqualSelectedDrawRates

/-! The actual initialized selected closure has measured preparation time,
complete local representation capacity/size, expected bit draw/read bounds,
independent whole players and every-completed-output height/hard budget.
The added closure's preparation lifetime and cross-reference allocation/
pricing schedule remain explicit obligations, outside this endpoint. -/
namespace Blotto.GeneralPaperEqualSelectedContract
open MeasureTheory
open GeneralPaperEqualInputDomain GeneralPaperEqualInputHeadline
open GeneralPaperEqualSelectedSampler (Sampler traceLaw observed outputLaw realDecode)
open GeneralPaperEqualSelectedPipeline (run)
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

theorem independent_players {n : ℕ} (model : RationalCostModel) {v : RationalFieldSelector n}
    {k : ℕ} {budget : ℚ} (a : Sampler v k budget) :
    let μ := (traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))
    Measure.map (Prod.map (realDecode model a) (realDecode model a)) (μ.prod μ) =
      (outputLaw model a : Measure (Allocation n)).prod (outputLaw model a : Measure (Allocation n)) :=
  GeneralPaperEqualBitBranchDraw.independent_players model a.address a.branch

theorem real_bit_law {n : ℕ} (model : RationalCostModel) {v : RationalFieldSelector n}
    {k : ℕ} {budget : ℚ} (a : Sampler v k budget) :
    outputLaw model a = GeneralPaperEqualRealBranch.outputLaw (GeneralPaperEqualBitBranch.realView a.branch) :=
  GeneralPaperEqualBitBranch.law_realView model a.branch

theorem exponent_bound {model : RationalCostModel} (p : Input model) : p.k ≤ binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ := by
  have h0 := GeneralPaperDyadicAccuracy.prepare_work (epsilon p)
  have h1 := GeneralPaperDyadicAccuracy.prepare_work_exact (epsilon p)
  rw [GeneralPaperEqualInputHeadline.exponent_exact]
  omega

theorem expected_reads (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    let a := (run model A K p).1
    (∫⁻ trace, ((observed model a trace).reads : ℝ≥0∞) ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
      (8388608 * (binaryWordWidth p.n + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ + 10) : ℕ) := by
  have h := GeneralPaperEqualSelectedDraw.expected_reads model (word K p) p.k p.values p.selector p.correct p.budget
    (run model A K p).1
  have hn : GeneralPaperEqualSelectedDraw.readsBound p.n p.k ≤
      8388608 * (binaryWordWidth p.n + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ + 10) := by
    have hk := exponent_bound p
    unfold GeneralPaperEqualSelectedDraw.readsBound
    omega
  exact h.trans (by exact_mod_cast hn)

theorem expected_work (model : RationalCostModel) {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (A K : ℕ) (p : Input model) :
    let a := (run model A K p).1
    (∫⁻ trace, ((observed model a trace).work : ℝ≥0∞) ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
      (17179869184 * C * (p.n + 1) * GeneralPaperEqualBitDrawRates.word p.n p.k (rationalWordWidth p.budget) *
        (GeneralPaperEqualBitDrawRates.log p.n p.k (rationalWordWidth p.budget)) ^ (d + 1) : ℕ) := by
  have h := GeneralPaperEqualSelectedDraw.expected_work model (word K p) p.k p.values p.selector p.correct p.budget
    (run model A K p).1
  exact h.trans (by exact_mod_cast GeneralPaperEqualSelectedDrawRates.fast_work_bound hg p.n p.k (rationalWordWidth p.budget))

theorem paper_time_and_returned_draw (model : RationalCostModel)
    (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ At et : ℕ, ∀ p : Input model,
      let result := run model (word K p) K p
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
  obtain ⟨At,et,ht⟩ := GeneralPaperEqualSelectedPipeline.paper_time model hFast K
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
    fun hOne hB => GeneralPaperEqualSelectedPipeline.epsilon model _ K p hOne hB⟩

end Blotto.GeneralPaperEqualSelectedContract
