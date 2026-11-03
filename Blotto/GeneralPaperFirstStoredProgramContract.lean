import Blotto.GeneralPaperFirstStoredSamplingContract

/-! Same-return complete corrected equal bit program, at any globally
chosen positive coefficient with its checked pointwise preparation capacity.
The common draw contract and its sharp rate concern this installed return. -/
namespace Blotto.GeneralPaperFirstStoredProgramContract
open MeasureTheory
open scoped ENNReal BigOperators
open GeneralPaperEqualInputDomain
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (Bounded cellSize)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

structure Contract (model : RationalCostModel) (K At et As es Ad ed : ℕ) (p : Input model)
    (output : Installed (GeneralPaperFirstStoredPipeline.width model 1 K p)) : Prop where
  returned : (GeneralPaperFirstStoredPipeline.run model 1 K p).1=some output
  measured_work : output.work=(GeneralPaperFirstStoredPipeline.run model 1 K p).2
  preparation_time : output.work ≤ At*GeneralPaperEqualInputHeadline.inputSize p*(GeneralPaperEqualInputHeadline.paperLog p)^et
  preparation_space : ∀ phase : GeneralPaperFirstStoredResources.Phase model K p,
    ∃ keys : Finset ℕ,(∀ key,GeneralPaperFirstStoredResources.resident model K p phase key≠none → key∈keys) ∧
      (∑ key∈keys,cellSize encode (GeneralPaperFirstStoredResources.resident model K p phase) key)+
          GeneralPaperFirstStoredResources.window model K p phase ≤
        As*GeneralPaperEqualInputHeadline.inputSize p*(GeneralPaperEqualInputHeadline.paperLog p)^es ∧
      (∑ key∈keys,cellSize encode (GeneralPaperFirstStoredResources.resident model K p phase) key)+
          GeneralPaperFirstStoredResources.window model K p phase < 2^word K p
  description : Bounded encode output.memory
    (2*GeneralPaperEqualDescriptionRates.paperBound p.n (p.k+1) (rationalWordWidth p.budget))
  sampling : GeneralPaperFirstStoredSamplingContract.Contract model 1 K p output
  draw_rate : GeneralPaperFirstStoredPipelineDrawWork.majorant model 1 K p ≤
    Ad*GeneralPaperFirstStoredDrawRates.inputScale p*(GeneralPaperFirstStoredDrawRates.drawLog p)^ed
  equilibrium : GeneralPaperEqualInputHeadline.epsilon p<1 → 0<p.budget →
    let a := (GeneralPaperEqualFirstInputPipeline.run model 1 K p).1;
    let μ := GeneralPaperStoredSelectedLaw.outputLaw model a.address output a.branch;
    Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤
      (GeneralPaperEqualInputHeadline.epsilon p : ℝ)

theorem uniform_resources (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (hK : 1≤K) :
    ∃ At et As es Ad ed : ℕ,∀ p : Input model,
      GeneralPaperFirstStoredCapacity.envelope model K p<2^word K p →
      ∃ output : Installed (GeneralPaperFirstStoredPipeline.width model 1 K p),Contract model K At et As es Ad ed p output := by
  obtain ⟨At,et,hTime⟩ := GeneralPaperFirstStoredWork.paper_time model hFast K
  obtain ⟨As,es,hSpace⟩ := GeneralPaperEqualInputHeadline.transfer_rate (GeneralPaperFirstStoredResources.profile_rate model hFast K)
  obtain ⟨Ad,ed,hDraw⟩ := GeneralPaperFirstStoredDrawRates.pipeline_rate model hFast 1 K
  refine ⟨At,et,As,es,Ad,ed,fun p hSafe => ?_⟩
  obtain ⟨output,hReturn,hWork,_⟩ := GeneralPaperFirstStoredPipeline.source model 1 K p
  have hW : 1≤word K p := Nat.mul_le_mul hK (logarithm_positive p)
  have hProfile : GeneralPaperFirstStoredResources.profile model K p<2^word K p := by
    dsimp only [GeneralPaperFirstStoredCapacity.envelope] at hSafe
    omega
  refine ⟨output,{
    returned := hReturn
    measured_work := hWork
    preparation_time := ?_
    preparation_space := ?_
    description := ?_
    sampling := GeneralPaperFirstStoredSamplingContract.every_returned model 1 K p output hReturn
    draw_rate := hDraw p
    equilibrium := fun hOne hB => GeneralPaperFirstStoredPipeline.epsilon model 1 K p hOne hB output hReturn
  }⟩
  · rw [hWork]
    exact (GeneralPaperFirstStoredWork.work_mono model 1 (word K p) K p hW).trans (hTime p)
  · intro phase
    obtain ⟨keys,hSupport,hBound⟩ := GeneralPaperFirstStoredResources.all_phases model K hK p phase
    exact ⟨keys,hSupport,hBound.trans (hSpace p),hBound.trans_lt hProfile⟩
  · exact GeneralPaperPayloadMemoryOwnership.mono encode _ _ _
      (GeneralPaperFirstStoredResident.pipeline_returned model 1 K p output hReturn)
      (GeneralPaperEqualFirstSelectedDescription.paper_bound model (word K p) p.k p.values p.selector p.correct p.budget _)

theorem calibrated_same_return (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es Ad ed : ℕ,1≤K ∧ ∀ p : Input model,
      ∃ output : Installed (GeneralPaperFirstStoredPipeline.width model 1 K p),Contract model K At et As es Ad ed p output := by
  obtain ⟨K,hK,hSafe⟩ := GeneralPaperFirstStoredCapacity.uniform_capacity model hFast
  obtain ⟨At,et,As,es,Ad,ed,h⟩ := uniform_resources model hFast K hK
  exact ⟨K,At,et,As,es,Ad,ed,hK,fun p => h p (hSafe p)⟩

end Blotto.GeneralPaperFirstStoredProgramContract
