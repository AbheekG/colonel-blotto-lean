import Blotto.GeneralPaperEqualCopiedPreparationCapacity

/-! The same actual initialized copied return has complete preparation and
copy phase space/capacity at one constructed word, sharp preparation time,
local description capacity, expected draws/reads, law/completion, rational
hard-budget outputs and continuous equilibrium. Actual measured pointer
layout/draw-access composition remains separate. -/
namespace Blotto.GeneralPaperEqualCopiedPreparationContract
open MeasureTheory
open GeneralPaperEqualInputDomain GeneralPaperEqualInputHeadline
open GeneralPaperEqualSelectedSampler (traceLaw observed outputLaw realDecode)
open GeneralPaperEqualCopiedPreparationResources
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

theorem all_phase_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (p : Input model) (phase : Phase model (word K p) p),
      window model (word K p) K p phase < 2 ^ word K p := by
  obtain ⟨K,hK,hSafe⟩ := GeneralPaperEqualCopiedPreparationCapacity.uniform_capacity model hFast
  refine ⟨K,hK,fun p phase => ?_⟩
  obtain ⟨hW,hIndex⟩ := GeneralPaperEqualDispatchContract.constructed_index_word K hK p
  exact (all_phases model _ K p hW hIndex phase).trans_lt (hSafe p)

theorem paper_time_space_and_returned_draw (model : RationalCostModel)
    (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es : ℕ, 1 ≤ K ∧ ∀ p : Input model,
      let W := word K p
      let result := GeneralPaperEqualCopiedPipeline.run model W K p
      let a := result.1
      result.2 ≤ At * inputSize p * (paperLog p) ^ et ∧
      (∀ phase : Phase model W p,
        window model W K p phase ≤ As * inputSize p * (paperLog p) ^ es ∧
        window model W K p phase < 2 ^ W) ∧
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
  obtain ⟨K,hK,hSafe⟩ := GeneralPaperEqualCopiedPreparationCapacity.uniform_capacity model hFast
  obtain ⟨At,et,hReturn⟩ := GeneralPaperEqualCopiedContract.paper_time_and_returned_draw model hFast K
  obtain ⟨As,es,hSpace⟩ := transfer_rate (GeneralPaperEqualCopiedPreparationCapacity.profile_rate model hFast K)
  refine ⟨K,At,et,As,es,hK,fun p => ?_⟩
  obtain ⟨ht,hDesc,hCapacity,hWork,hReads,hLaw,hAE,hOutput,hEq⟩ := hReturn p
  refine ⟨ht,?_,hDesc,hCapacity,hWork,hReads,hLaw,hAE,hOutput,hEq⟩
  intro phase
  obtain ⟨hW,hIndex⟩ := GeneralPaperEqualDispatchContract.constructed_index_word K hK p
  have hs := all_phases model _ K p hW hIndex phase
  exact ⟨hs.trans (hSpace p),hs.trans_lt (hSafe p)⟩

theorem expected_reads (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    let a := (GeneralPaperEqualCopiedPipeline.run model A K p).1
    (∫⁻ trace, ((observed model a trace).reads : ℝ≥0∞) ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
      (8388608 * (binaryWordWidth p.n + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ + 10) : ℕ) := by
  have h := GeneralPaperEqualSelectedDraw.expected_reads model (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualCopiedPipeline.run model A K p).1
  have hn : GeneralPaperEqualSelectedDraw.readsBound p.n p.k ≤
      8388608 * (binaryWordWidth p.n + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ + 10) := by
    have hk := GeneralPaperEqualSelectedContract.exponent_bound p
    unfold GeneralPaperEqualSelectedDraw.readsBound
    omega
  exact h.trans (by exact_mod_cast hn)

theorem expected_work (model : RationalCostModel) {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (A K : ℕ) (p : Input model) :
    let a := (GeneralPaperEqualCopiedPipeline.run model A K p).1
    (∫⁻ trace, ((observed model a trace).work : ℝ≥0∞) ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
      (17179869184 * C * (p.n + 1) * GeneralPaperEqualBitDrawRates.word p.n p.k (rationalWordWidth p.budget) *
        (GeneralPaperEqualBitDrawRates.log p.n p.k (rationalWordWidth p.budget)) ^ (d + 1) : ℕ) := by
  have h := GeneralPaperEqualSelectedDraw.expected_work model (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualCopiedPipeline.run model A K p).1
  exact h.trans (by exact_mod_cast GeneralPaperEqualSelectedDrawRates.fast_work_bound hg p.n p.k (rationalWordWidth p.budget))

theorem independent_players (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    let a := (GeneralPaperEqualCopiedPipeline.run model A K p).1
    let μ := (traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))
    Measure.map (Prod.map (realDecode model a) (realDecode model a)) (μ.prod μ) =
      (outputLaw model a : Measure (Allocation p.n)).prod (outputLaw model a : Measure (Allocation p.n)) :=
  GeneralPaperEqualSelectedContract.independent_players model _

end Blotto.GeneralPaperEqualCopiedPreparationContract
