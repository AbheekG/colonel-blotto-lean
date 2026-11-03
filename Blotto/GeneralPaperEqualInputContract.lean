import Blotto.GeneralPaperEqualInputPipeline

/-! Branch-unrestricted original-input endpoint for the actual initialized
bit return. Complete measured preparation time and every initializer cursor
are checked together with its continuous law and observed bit-output law.
Dispatch/native phase-space and representation joins remain explicit. -/
namespace Blotto.GeneralPaperEqualInputContract
open MeasureTheory
open GeneralPaperEqualInputDomain
open GeneralPaperEqualBitBranch (outputLaw)
set_option autoImplicit false
set_option maxHeartbeats 2200000

theorem paper_time_initializer_space_and_equilibrium (model : RationalCostModel)
    (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es : ℕ, 1 ≤ K ∧ ∀ p : Input model,
      let W := word K p
      let result := GeneralPaperEqualInputPipeline.run model W K p
      result.2 ≤ At * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ et ∧
      (∀ phase : GeneralPaperEqualInputInitializerLifetime.Phase p.n,
        GeneralPaperEqualInputInitializerLifetime.window model W K p phase ≤
          As * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ es ∧
        GeneralPaperEqualInputInitializerLifetime.window model W K p phase < 2 ^ W) ∧
      (GeneralPaperEqualInputHeadline.epsilon p < 1 → 0 < p.budget →
        Supported (p.budget : ℝ) (outputLaw model result.1) ∧
        regret p.selector.values (p.budget : ℝ) (outputLaw model result.1) (outputLaw model result.1) ≤
          (GeneralPaperEqualInputHeadline.epsilon p : ℝ)) := by
  obtain ⟨K, At, et, As, es, hK, h⟩ := GeneralPaperEqualInputHeadline.measured_time_initializer_space model hFast
  refine ⟨K, At, et, As, es, hK, fun p => ?_⟩
  obtain ⟨_, _, ht, hs⟩ := h p
  refine ⟨?_, hs, fun hOne hB => GeneralPaperEqualInputPipeline.epsilon model _ K p hOne hB⟩
  rw [GeneralPaperEqualInputPipeline.calibrated_work]
  exact ht

theorem actual_trace_law (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    let branch := (GeneralPaperEqualInputPipeline.run model A K p).1
    (GeneralPaperEqualBitBranchDraw.traceLaw branch).map (GeneralPaperEqualBitBranchDraw.realDecode model (word K p) branch) =
      outputLaw model branch := GeneralPaperEqualBitBranchDraw.law model _ _

theorem independent_players (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    let branch := (GeneralPaperEqualInputPipeline.run model A K p).1
    let μ := (GeneralPaperEqualBitBranchDraw.traceLaw branch : Measure (GeneralPaperEqualBitBranchDraw.Trace branch))
    let f := GeneralPaperEqualBitBranchDraw.realDecode model (word K p) branch
    Measure.map (Prod.map f f) (μ.prod μ) =
      (outputLaw model branch : Measure (Allocation p.n)).prod (outputLaw model branch : Measure (Allocation p.n)) :=
  GeneralPaperEqualBitBranchDraw.independent_players model _ _

theorem completed_ae (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    let branch := (GeneralPaperEqualInputPipeline.run model A K p).1
    ∀ᵐ trace ∂(GeneralPaperEqualBitBranchDraw.traceLaw branch : Measure (GeneralPaperEqualBitBranchDraw.Trace branch)),
      ∃ row, (GeneralPaperEqualBitBranchDraw.observed model (word K p) branch trace).output = some row :=
  GeneralPaperEqualBitBranchDraw.completed_ae model _ _

theorem every_completed_budget (model : RationalCostModel) (A K : ℕ) (p : Input model) (hB : 0 ≤ p.budget) :
    let branch := (GeneralPaperEqualInputPipeline.run model A K p).1
    ∀ trace row, (GeneralPaperEqualBitBranchDraw.observed model (word K p) branch trace).output = some row →
      FullBudget (p.budget : ℝ) row.realAllocation := by
  dsimp only
  intro trace row h
  exact GeneralPaperEqualBitBranchDraw.completed_budget model _ _ hB trace row h

end Blotto.GeneralPaperEqualInputContract
