import Blotto.GeneralPaperFirstAllBitLaw

/-! The retained-word equal return has the established canonical law and
pointwise original-budget guarantees, for every initializer price word. -/
namespace Blotto.GeneralPaperFirstMeasuredEqualContract
open GeneralPaperOriginalGameInput GeneralPaperAllBranchBitDispatch GeneralPaperFirstAllBitLaw
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem canonical_source (model : RationalCostModel) (A K : ℕ) (p : Input) :
    (GeneralPaperEqualFirstInputPipeline.run model A K (equalInput model p)).1 = equalSource model K p := by
  simp only [equalSource, GeneralPaperEqualFirstInputPipeline.data]

theorem equilibrium (model : RationalCostModel) (A K : ℕ) (p : Input) (hB : p.budget = 1)
    (hOne : epsilon p < 1)
    (output : GeneralPaperUnifiedDirectoryInstallation.Installed
      (GeneralPaperFirstStoredPipeline.width model A K (equalInput model p)))
    (hReturn : (GeneralPaperFirstStoredPipeline.run model A K (equalInput model p)).1 = some output) :
    Guarantee model K p (.equal _ output) := by
  have h := GeneralPaperFirstStoredPipeline.epsilon model A K (equalInput model p) hOne p.budget_valid.1 output hReturn
  dsimp only at h
  rw [canonical_source] at h
  change Supported (p.budget : ℝ) (law model K p (.equal _ output) false) ∧
    regret p.selector.values (p.budget : ℝ) (law model K p (.equal _ output) false)
      (law model K p (.equal _ output) false) ≤ (epsilon p : ℝ) at h
  change Supported 1 (law model K p (.equal _ output) false) ∧
    Supported (p.budget : ℝ) (law model K p (.equal _ output) false) ∧ _ ∧ _
  rw [hB, Rat.cast_one] at h ⊢
  exact ⟨h.1, h.1, h.2, h.2⟩

theorem pointwise (model : RationalCostModel) (A K : ℕ) (p : Input) (hB : p.budget = 1)
    (output : GeneralPaperUnifiedDirectoryInstallation.Installed
      (GeneralPaperFirstStoredPipeline.width model A K (equalInput model p)))
    (hReturn : (GeneralPaperFirstStoredPipeline.run model A K (equalInput model p)).1 = some output) :
    Pointwise model K p (.equal _ output) := by
  dsimp only [Pointwise]
  rw [← canonical_source model A K p]
  intro trace row hOutput
  have h := GeneralPaperFirstStoredOutput.pipeline_written_output model A K (equalInput model p)
    p.budget_valid.1.le output hReturn trace row hOutput
  change row.size = p.n ∧ FullBudget (p.budget : ℝ) _ ∧ _ at h
  rw [hB, Rat.cast_one] at h ⊢
  exact ⟨h.1, h.2.1, h.2.1⟩

theorem constructed (model : RationalCostModel) (A K : ℕ) (p : Input) (hB : p.budget = 1)
    (hOne : epsilon p < 1) :
    ∃ output, (GeneralPaperFirstMeasuredEqualPreparation.run model A K p).1 = some output ∧
      Guarantee model K p output ∧ Pointwise model K p output := by
  obtain ⟨output, hReturn, hPipeline⟩ := GeneralPaperFirstMeasuredEqualPreparation.returns model A K p
  exact ⟨.equal _ output, hReturn, equilibrium model A K p hB hOne output hPipeline,
    pointwise model A K p hB output hPipeline⟩

theorem sampled_return (model : RationalCostModel) (K : ℕ) (p : Input) (hB : p.budget = 1)
    (hOne : epsilon p < 1) :
    ∃ output : GeneralPaperUnifiedDirectoryInstallation.Installed
        (GeneralPaperFirstStoredPipeline.width model 1 K (equalInput model p)),
      (GeneralPaperFirstMeasuredEqualPreparation.run model 1 K p).1 = some (.equal _ output) ∧
      Guarantee model K p (.equal _ output) ∧ Pointwise model K p (.equal _ output) ∧
      GeneralPaperFirstStoredSamplingContract.Contract model 1 K (equalInput model p) output := by
  obtain ⟨output, hReturn, hPipeline⟩ := GeneralPaperFirstMeasuredEqualPreparation.returns model 1 K p
  exact ⟨output, hReturn, equilibrium model 1 K p hB hOne output hPipeline,
    pointwise model 1 K p hB output hPipeline,
    GeneralPaperFirstStoredSamplingContract.every_returned model 1 K (equalInput model p) output hPipeline⟩

end Blotto.GeneralPaperFirstMeasuredEqualContract
