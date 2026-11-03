import Blotto.GeneralPaperEqualInitializedPreparation
import Blotto.GeneralPaperEqualFullBitOutput

/-! Contracts for the same sampler returned by measured initialization and
preparation. Numerical address capacity is explicit; allocation/layout and
the other raw-input branches are separate obligations. -/
namespace Blotto.GeneralPaperEqualInitializedContract
open MeasureTheory
open scoped ENNReal
open GeneralPaperEqualResourceDomain
open GeneralPaperEqualInitializedPreparation (run data)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem expected_work (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    let sampler := (run model A K p).1
    (∫⁻ trace, ((GeneralPaperEqualStoredBitSampler.observed sampler model trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D sampler.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
          Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) ≤
      (GeneralPaperEqualFullBitContract.bound model p.n p.k (rationalWordWidth p.budget) : ℝ≥0∞) := by
  dsimp only
  rw [data]
  exact GeneralPaperEqualFullBitContract.native_expected_work true model _ p.k
    p.values p.selector p.correct (small_at_reference p _) p.budget

theorem completed_ae (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    let sampler := (run model A K p).1
    ∀ᵐ trace ∂(law sampler.prepared.D sampler.prepared.midpointBits
      (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
        Measure (Trace sampler.prepared.D sampler.prepared.midpointBits)),
      ∃ row, (GeneralPaperEqualStoredBitSampler.observed sampler model trace).output = some row := by
  dsimp only
  exact GeneralPaperEqualFullBitOutput.completed_ae _ model _

theorem expected_reads (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    let sampler := (run model A K p).1
    (∫⁻ trace, ((GeneralPaperEqualStoredBitSampler.observed sampler model trace).reads : ℝ≥0∞)
      ∂(law sampler.prepared.D sampler.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
          Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) =
      ENNReal.ofReal ((UniformNatRejection.width sampler.prepared.D : ℝ) /
        (UniformNatRejection.acceptance sampler.prepared.D : ℝ) + sampler.prepared.midpointBits) := by
  dsimp only
  exact GeneralPaperEqualFullBitOutput.expected_reads_exact _ model _

theorem independent_players (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    let sampler := (run model A K p).1
    let μ := (law sampler.prepared.D sampler.prepared.midpointBits
      (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
        Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))
    let f := GeneralPaperEqualFullBitDraw.realDecode sampler.categorical model sampler.address
    Measure.map (Prod.map f f) (μ.prod μ) =
      (GeneralPaperEqualStoredBitSampler.outputLaw sampler model : Measure (Allocation p.n)).prod
        (GeneralPaperEqualStoredBitSampler.outputLaw sampler model : Measure (Allocation p.n)) := by
  dsimp only
  exact GeneralPaperEqualFullBitOutput.independent_traces _ model _

theorem real_bit_law (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    let sampler := (run model A K p).1
    GeneralPaperEqualStoredBitSampler.outputLaw sampler model =
      GeneralPaperEqualRealDraw.outputLaw sampler.prepared := by
  exact GeneralPaperEqualFullBitOutput.real_bit_law _ model

theorem written_output (model : RationalCostModel) (A K : ℕ) (p : Problem model)
    (hB : 0 ≤ p.budget) {b : ℕ} (hHeight : RationalHeight p.budget b) :
    let sampler := (run model A K p).1
    ∀ (cap : ℕ)
      (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool)
      (fresh : Fin sampler.prepared.midpointBits → Bool) (row : RationalResourceArray p.n),
      (GeneralPaperEqualStoredBitSampler.run sampler model cap tape fresh).output = some row →
      FullBudget (p.budget : ℝ) row.realAllocation ∧
        ∀ j, RationalHeight (row.allocation j) (33554432 * (b + binaryWordWidth p.n + p.k + 10)) := by
  dsimp only
  rw [data]
  intro cap tape fresh row h
  exact GeneralPaperEqualFullBitOutput.native_written_output true model _ p.k
    p.values p.selector p.correct (small_at_reference p _) p.budget hB hHeight cap tape fresh row h

/-- One uniform coefficient gives complete measured preparation prices and
all defined phase reserves for the actual returned law-certified sampler.
Its retained data also fits its distinct, already stored draw reference. -/
theorem paper_contract (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es : ℕ, 1 ≤ K ∧ ∀ p : Problem model,
      let W := GeneralPaperEqualCommonReference.word K p
      let result := run model W K p
      result.2 ≤ At * GeneralPaperEqualResourceHeadline.inputSize p *
        (GeneralPaperEqualResourceHeadline.paperLog p) ^ et ∧
      (∀ phase : GeneralPaperEqualFullInitializationResources.Phase model W p,
        GeneralPaperEqualFullInitializationResources.window model W K p phase ≤
          As * GeneralPaperEqualResourceHeadline.inputSize p * (GeneralPaperEqualResourceHeadline.paperLog p) ^ es ∧
        GeneralPaperEqualFullInitializationResources.window model W K p phase < 2 ^ W) ∧
      GeneralPaperEqualRetainedStorage.footprint result.1.address result.1 < 2 ^ result.1.address ∧
      (GeneralPaperEqualResourceHeadline.epsilon p < 1 → 0 < p.budget →
        Supported (p.budget : ℝ) (GeneralPaperEqualStoredBitSampler.outputLaw result.1 model) ∧
          regret p.selector.values (p.budget : ℝ)
            (GeneralPaperEqualStoredBitSampler.outputLaw result.1 model)
            (GeneralPaperEqualStoredBitSampler.outputLaw result.1 model) ≤
              (GeneralPaperEqualResourceHeadline.epsilon p : ℝ)) := by
  obtain ⟨K, At, et, As, es, hK, h⟩ := GeneralPaperEqualFullInitializationResources.time_space_capacity model hFast
  refine ⟨K, At, et, As, es, hK, fun p => ?_⟩
  obtain ⟨_, _, ht, hs⟩ := h p
  refine ⟨?_, hs, GeneralPaperEqualInitializedPreparation.returned_capacity model _ K p,
    fun hOne hB => GeneralPaperEqualInitializedPreparation.epsilon model _ K p hOne hB⟩
  rw [GeneralPaperEqualInitializedPreparation.calibrated_work]
  exact ht

end Blotto.GeneralPaperEqualInitializedContract
