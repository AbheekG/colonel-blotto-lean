import Blotto.GeneralPaperMeasuredEqualWork

/-! Explicit work of the measured dispatcher and one global calibration
joined to its actual original-game return. Complete unequal time and the
combined physical lifetime/description/draw headlines remain separate. -/
namespace Blotto.GeneralPaperMeasuredDispatchResources
open GeneralPaperOriginalGameInput GeneralPaperMeasuredBitDispatch
open GeneralPaperAllBranchBitDispatch (Prepared branchPrice)
open GeneralPaperAllBranchBitLaw (Guarantee)
open GeneralPaperAllBranchBitOutput (Pointwise)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem one_work (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) :
    (run model K p).2 ≤ 288 * (rationalWordWidth p.budget + 3) + 64 + 64 * (binaryWordWidth p.n + 1) := by
  rw [on_one model K p hN]
  have h := GeneralPaperOneFieldRealPreparation.work 1 p.budget
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) 64) _

theorem equal_work (model : RationalCostModel) (K : ℕ) (hK : 1 ≤ K) (p : Input)
    (hN : p.n ≠ 1) (hB : p.budget = 1) :
    (run model K p).2 ≤ GeneralPaperCompleteStoredPipelineWork.price model K (equalInput model p) + branchPrice model p := by
  rw [on_equal model K p hN hB]
  exact Nat.add_le_add_right (GeneralPaperMeasuredEqualWork.work model K hK p) _

theorem unequal_work (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n ≠ 1) (hB : p.budget ≠ 1) :
    (run model K p).2 ≤
      GeneralPaperEqualInputInitialization.initializationPrice model 1 K (equalInput model p) +
      (GeneralPaperClosedStrategyDriver.bit model
        (K * GeneralPaperOriginalReferenceComparison.logarithm model p)
        (K * GeneralPaperOriginalReferenceComparison.logarithm model p)
        (K * GeneralPaperOriginalReferenceComparison.logarithm model p)
        p.words p.values p.selector p.correct p.budget ⟨p.budget_valid.1, strict_of_ne p hB⟩).2 +
      64 * (1 + K * GeneralPaperOriginalReferenceComparison.logarithm model p + 1) + branchPrice model p := by
  rw [on_unequal model K p hN hB]
  exact Nat.add_le_add_right (GeneralPaperMeasuredUnequalPreparation.work model 1 K p (strict_of_ne p hB)) _

theorem calibrated_original_game_contract {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (p : Input), epsilon p < 1 →
      ∃ output : Prepared p.n, (run model K p).1 = some output ∧ Guarantee model K p output ∧ Pointwise model K p output ∧
      GeneralPaperStoredPreparationUniformCapacity.envelope model K (equalInput model p) <
        2 ^ (GeneralPaperOriginalMeasuredReference.prepare model 1 K p).1.2 ∧ ∀ h : p.budget < 1,
      GeneralPaperNativeResourceReferenceGrowth.word model C d (unequalInput p h) ≤
        (GeneralPaperOriginalMeasuredReference.prepare model 1 K p).1.2 ∧
      GeneralPaperNativeResourceReferenceGrowth.reserve model C d
        (GeneralPaperOriginalMeasuredReference.prepare model 1 K p).1.2 (unequalInput p h) <
        2 ^ (GeneralPaperOriginalMeasuredReference.prepare model 1 K p).1.2 := by
  obtain ⟨K, hK, hCapacity⟩ := GeneralPaperOriginalMeasuredReference.uniform_capacity hg
  refine ⟨K, hK, fun p hOne => ?_⟩
  obtain ⟨output, hReturn, hLaw, hPointwise⟩ := original_game_contract model K p hOne
  exact ⟨output, hReturn, hLaw, hPointwise, (hCapacity p 1).1, (hCapacity p 1).2⟩

theorem equal_sampling_and_work (model : RationalCostModel) (K : ℕ) (hK : 1 ≤ K) (p : Input)
    (hN : p.n ≠ 1) (hB : p.budget = 1) (hOne : epsilon p < 1) :
    ∃ output : GeneralPaperUnifiedDirectoryInstallation.Installed
        (GeneralPaperStoredSelectedPipeline.width model 1 K (equalInput model p)),
      (run model K p).1 = some (.equal _ output) ∧
      Guarantee model K p (.equal _ output) ∧ Pointwise model K p (.equal _ output) ∧
      GeneralPaperStoredPipelineSamplingContract.Contract model 1 K (equalInput model p) output ∧
      (run model K p).2 ≤ GeneralPaperCompleteStoredPipelineWork.price model K (equalInput model p) + branchPrice model p := by
  obtain ⟨output, hReturn, hLaw, hPointwise, hSampling⟩ := GeneralPaperMeasuredEqualContract.sampled_return model K p hB hOne
  refine ⟨output, ?_, hLaw, hPointwise, hSampling, equal_work model K hK p hN hB⟩
  rw [on_equal model K p hN hB]
  exact hReturn

theorem equal_independent_players (model : RationalCostModel) (K : ℕ) (p : Input)
    (hN : p.n ≠ 1) (hB : p.budget = 1) :
    ∃ output : GeneralPaperUnifiedDirectoryInstallation.Installed
        (GeneralPaperStoredSelectedPipeline.width model 1 K (equalInput model p)),
      (run model K p).1 = some (.equal _ output) ∧
      let branch := (GeneralPaperEqualCopiedPipeline.run model 1 K (equalInput model p)).1.branch
      let μ := (GeneralPaperEqualBitBranchDraw.traceLaw branch : MeasureTheory.Measure (GeneralPaperEqualBitBranchDraw.Trace branch))
      let decode := GeneralPaperStoredSelectedLaw.realDecode model
        (GeneralPaperStoredSelectedPipeline.width model 1 K (equalInput model p)) output branch
      MeasureTheory.Measure.map (Prod.map decode decode) (μ.prod μ) =
        (GeneralPaperStoredSelectedLaw.outputLaw model
          (GeneralPaperStoredSelectedPipeline.width model 1 K (equalInput model p)) output branch :
          MeasureTheory.Measure (Allocation (equalInput model p).n)).prod
        (GeneralPaperStoredSelectedLaw.outputLaw model
          (GeneralPaperStoredSelectedPipeline.width model 1 K (equalInput model p)) output branch :
          MeasureTheory.Measure (Allocation (equalInput model p).n)) := by
  obtain ⟨output, hReturn, _⟩ := GeneralPaperMeasuredEqualPreparation.returns model 1 K p
  refine ⟨output, ?_, GeneralPaperStoredPipelineSamplingContract.independent_players model 1 K (equalInput model p) output⟩
  rw [on_equal model K p hN hB]
  exact hReturn

end Blotto.GeneralPaperMeasuredDispatchResources
