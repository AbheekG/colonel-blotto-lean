import Blotto.GeneralPaperStoredPreparationUniformCapacity

/-! One fixed preparation coefficient joins the actual stored pipeline's
complete work, all preparation phase space/capacity bounds, caller controls
and the canonical continuous epsilon law on the same returned object.
Explicit paper powers, draw and other entry branches are separate joins. -/
namespace Blotto.GeneralPaperStoredPreparationPaperContract
open GeneralPaperEqualInputDomain
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open GeneralPaperStoredPreparationPhases (Phase resident window profile)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192

theorem time_space_capacity_equilibrium (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K Ct dt Cs ds : ℕ,1 ≤ K ∧ ∀ p : Input model,
      (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).2 ≤
        Ct * GeneralPaperEqualInputHeadline.inputSize p * GeneralPaperEqualInputHeadline.paperLog p ^ dt ∧
      GeneralPaperCompleteStoredPipelineWork.price model K p < 2 ^ word K p ∧
      (∀ value ∈ GeneralPaperPreparationCallerControls.controls model K p,value < 2 ^ word K p) ∧
      (∀ phase : Phase model K p,∃ keys : Finset ℕ,
        (∀ key,resident model K p phase key ≠ none → key ∈ keys) ∧
        (∑ key ∈ keys,cellSize encode (resident model K p phase) key) + window model K p phase ≤
          Cs * GeneralPaperEqualInputHeadline.inputSize p * GeneralPaperEqualInputHeadline.paperLog p ^ ds ∧
        (∑ key ∈ keys,cellSize encode (resident model K p phase) key) + window model K p phase < 2 ^ word K p) ∧
      (GeneralPaperEqualInputHeadline.epsilon p < 1 → 0 < p.budget →
        ∃ returned : Installed (GeneralPaperStoredSelectedPipeline.width model (word K p) K p),
          (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1 = some returned ∧
          returned.work = (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).2 ∧
          let μ := GeneralPaperStoredSelectedLaw.outputLaw model
            (GeneralPaperStoredSelectedPipeline.width model (word K p) K p) returned
            (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.branch
          Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤
            (GeneralPaperEqualInputHeadline.epsilon p : ℝ)) := by
  obtain ⟨K,hK,hSafe⟩ := GeneralPaperStoredPreparationUniformCapacity.uniform_capacity model hFast
  obtain ⟨Ct,dt,hTime⟩ := GeneralPaperCompleteStoredPipelineWork.paper_time model hFast K
  obtain ⟨Cs,ds,hSpace⟩ := GeneralPaperEqualInputHeadline.transfer_rate
    (GeneralPaperStoredPreparationPhases.profile_rate model hFast K)
  refine ⟨K,Ct,dt,Cs,ds,hK,fun p => ?_⟩
  have hProfile : profile model K p < 2 ^ word K p := by
    have h := hSafe p
    dsimp only [GeneralPaperStoredPreparationUniformCapacity.envelope] at h
    omega
  have hCap : GeneralPaperPreparationCallerControls.cap model K p < 2 ^ word K p := by
    have h := hSafe p
    dsimp only [GeneralPaperStoredPreparationUniformCapacity.envelope] at h
    omega
  have hPrice : GeneralPaperCompleteStoredPipelineWork.price model K p < 2 ^ word K p := by
    apply lt_of_le_of_lt _ hCap
    unfold GeneralPaperPreparationCallerControls.cap
    omega
  refine ⟨hTime p,hPrice,
    fun value hv => (GeneralPaperPreparationCallerControls.fields_bounded model K p value hv).trans_lt hCap,?_,?_⟩
  · intro phase
    obtain ⟨keys,hSupport,hBound⟩ := GeneralPaperStoredPreparationPhases.all_phases model K hK p phase
    exact ⟨keys,hSupport,hBound.trans (hSpace p),hBound.trans_lt hProfile⟩
  · intro hOne hBudget
    obtain ⟨returned,hReturn,hWork,_hCost,hLaw⟩ := GeneralPaperCompleteStoredPipelineWork.epsilon_constructed K p hOne hBudget
    exact ⟨returned,hReturn,hWork,hLaw⟩

end Blotto.GeneralPaperStoredPreparationPaperContract
