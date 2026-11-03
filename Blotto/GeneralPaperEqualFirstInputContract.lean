import Blotto.GeneralPaperEqualFirstInputCapacity

/-! A single actual original-input return has the paper's corrected source,
computed common preparation width, all phase-space/time bounds, compact
local description, exact independent draws and canonical equilibrium.
Installation into the shared stored-memory dispatcher is a later join. -/
namespace Blotto.GeneralPaperEqualFirstInputContract
open MeasureTheory
open scoped ENNReal
open GeneralPaperEqualInputDomain
open GeneralPaperEqualInputHeadline (inputSize paperLog epsilon)
open GeneralPaperEqualSelectedSampler (traceLaw observed realDecode outputLaw)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem actual_time (model : RationalCostModel) (K : ℕ) (p : Input model) (hK : 1 ≤ K) :
    (GeneralPaperEqualFirstInputPipeline.run model 1 K p).2 ≤
      (GeneralPaperEqualFirstInputPipeline.run model (word K p) K p).2 := by
  rw [GeneralPaperEqualFirstInputPipeline.work,GeneralPaperEqualFirstInputPipeline.work]
  exact Nat.add_le_add_right (GeneralPaperMeasuredInitializerMonotonicity.initialization model 1 (word K p) K
    (Nat.mul_le_mul hK (logarithm_positive p)) p) _

theorem actual_contract (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es : ℕ,1 ≤ K ∧ ∀ p : Input model,
      let W := word K p
      let result := GeneralPaperEqualFirstInputPipeline.run model 1 K p
      let a := result.1
      (GeneralPaperEqualInputInitialization.prepareReference model 1 K p).1.1 = p.k ∧
      (GeneralPaperEqualInputInitialization.prepareReference model 1 K p).1.2 = W ∧
      result.2 ≤ At*inputSize p*(paperLog p)^et ∧
      (∀ phase : GeneralPaperEqualFirstInputResources.Phase model W p,
        GeneralPaperEqualFirstInputResources.window model W 1 K p phase ≤ As*inputSize p*(paperLog p)^es ∧
        GeneralPaperEqualFirstInputResources.window model W 1 K p phase < 2^W) ∧
      GeneralPaperEqualSelectedDescription.footprint a ≤
        2*GeneralPaperEqualDescriptionRates.paperBound p.n (p.k+1) (rationalWordWidth p.budget) ∧
      GeneralPaperEqualSelectedDescription.footprint a < 2^a.address ∧
      (traceLaw a).map (realDecode model a) = outputLaw model a ∧
      (∀ᵐ trace ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch)),
        ∃ row,(observed model a trace).output = some row) ∧
      (0 ≤ p.budget → ∀ trace row,(observed model a trace).output = some row →
        FullBudget (p.budget : ℝ) row.realAllocation ∧ ∀ j,
          RationalHeight (row.allocation j) (GeneralPaperEqualBitDrawRates.word p.n (p.k+1) (rationalWordWidth p.budget))) ∧
      (∫⁻ trace,((observed model a trace).reads : ℝ≥0∞)
        ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
          (GeneralPaperEqualFirstBitSampling.readsBound p.n p.k : ℝ≥0∞) ∧
      (∫⁻ trace,((observed model a trace).work : ℝ≥0∞)
        ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
          (GeneralPaperEqualSelectedDraw.workBound model p.n (p.k+1) (rationalWordWidth p.budget) : ℝ≥0∞) ∧
      (epsilon p < 1 → 0 < p.budget → Supported (p.budget : ℝ) (outputLaw model a) ∧
        regret p.selector.values (p.budget : ℝ) (outputLaw model a) (outputLaw model a) ≤ (epsilon p : ℝ)) := by
  obtain ⟨K,hK,hSafe⟩ := GeneralPaperEqualFirstInputCapacity.uniform_capacity model hFast
  obtain ⟨At,et,hTime⟩ := GeneralPaperEqualFirstInputPipeline.paper_time model hFast K
  obtain ⟨As,es,hSpace⟩ := GeneralPaperEqualInputHeadline.transfer_rate
    (GeneralPaperEqualFirstInputCapacity.profile_rate model hFast K)
  refine ⟨K,At,et,As,es,hK,fun p => ?_⟩
  dsimp only
  let a := (GeneralPaperEqualFirstInputPipeline.run model 1 K p).1
  have hData := GeneralPaperEqualFirstInputPipeline.data model 1 K p
  have hDesc := GeneralPaperEqualFirstSelectedDescription.paper_bound model (word K p) p.k p.values p.selector p.correct p.budget a
  have hCapacity := GeneralPaperEqualFirstSelectedDescription.capacity model (word K p) p.k p.values p.selector p.correct p.budget a
  refine ⟨GeneralPaperEqualInputInitialization.initialized_exponent model 1 K p,
    GeneralPaperEqualInputInitialization.initialized_word model 1 K p,
    (actual_time model K p hK).trans (hTime p),?_,hDesc,hCapacity,
    GeneralPaperEqualSelectedSampler.law model a,GeneralPaperEqualSelectedSampler.completed_ae model a,?_,
    GeneralPaperEqualFirstBitSampling.expected_reads model (word K p) a.address p.k p.values p.selector p.correct p.budget a.branch,
    GeneralPaperEqualFirstBitWork.expected_work model (word K p) p.k p.values p.selector p.correct p.budget a,
    fun hOne hB => GeneralPaperEqualFirstInputPipeline.epsilon model 1 K p hOne hB⟩
  · intro phase
    obtain ⟨hW,hIndex⟩ := GeneralPaperEqualDispatchContract.constructed_index_word K hK p
    have hs := GeneralPaperEqualFirstInputResources.all_phases model (word K p) 1 K p hW hIndex hW phase
    exact ⟨hs.trans (hSpace p),hs.trans_lt (hSafe p)⟩
  · intro hB trace row hRow
    exact ⟨GeneralPaperEqualSelectedSampler.completed_budget model a hB trace row hRow,
      GeneralPaperEqualFirstBitOutput.completed_height model (word K p) a.address p.k p.values p.selector p.correct p.budget
        (rationalHeight_of_wordWidth p.budget) a.branch trace row hRow⟩

theorem independent_players (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    let a := (GeneralPaperEqualFirstInputPipeline.run model A K p).1
    let μ := (traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))
    Measure.map (Prod.map (realDecode model a) (realDecode model a)) (μ.prod μ) =
      (outputLaw model a : Measure (Allocation p.n)).prod (outputLaw model a : Measure (Allocation p.n)) :=
  GeneralPaperEqualBitBranchDraw.independent_players model _ _

end Blotto.GeneralPaperEqualFirstInputContract
