import Blotto.GeneralPaperFirstStoredOutput

/-! One actual installed corrected return joins computed-word full
preparation time/space/capacity, finite resident description, canonical law,
exact completion, every-output budgets/heights and expected fresh bits.
Complete stored draw-work and the shared all-branch headline remain separate. -/
namespace Blotto.GeneralPaperFirstStoredContract
open MeasureTheory
open scoped ENNReal BigOperators
open GeneralPaperEqualInputDomain
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (Bounded cellSize)
open GeneralPaperEqualBitBranchDraw (Trace traceLaw)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem actual_contract (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es : ℕ,1 ≤ K ∧ ∀ p : Input model,
      ∃ output : Installed (GeneralPaperFirstStoredPipeline.width model 1 K p),
        (GeneralPaperFirstStoredPipeline.run model 1 K p).1=some output ∧
        output.work=(GeneralPaperFirstStoredPipeline.run model 1 K p).2 ∧
        output.work ≤ At*GeneralPaperEqualInputHeadline.inputSize p*(GeneralPaperEqualInputHeadline.paperLog p)^et ∧
        (∀ phase : GeneralPaperFirstStoredResources.Phase model K p,
          ∃ keys : Finset ℕ,(∀ key,GeneralPaperFirstStoredResources.resident model K p phase key ≠ none → key ∈ keys) ∧
            (∑ key ∈ keys,cellSize encode (GeneralPaperFirstStoredResources.resident model K p phase) key)+
                GeneralPaperFirstStoredResources.window model K p phase ≤
              As*GeneralPaperEqualInputHeadline.inputSize p*(GeneralPaperEqualInputHeadline.paperLog p)^es ∧
            (∑ key ∈ keys,cellSize encode (GeneralPaperFirstStoredResources.resident model K p phase) key)+
                GeneralPaperFirstStoredResources.window model K p phase < 2^word K p) ∧
        Bounded encode output.memory (2*GeneralPaperEqualDescriptionRates.paperBound p.n (p.k+1) (rationalWordWidth p.budget)) ∧
        (let a := (GeneralPaperEqualFirstInputPipeline.run model 1 K p).1;
          GeneralPaperStoredSelectedLaw.outputLaw model a.address output a.branch=GeneralPaperEqualSelectedSampler.outputLaw model a ∧
          GeneralPaperEqualSelectedDescription.footprint a<2^a.address ∧
          (∀ᵐ trace ∂(traceLaw a.branch : Measure (Trace a.branch)),
            ∃ row,(GeneralPaperStoredSelectedLaw.observed model a.address output a.branch trace).output=some row) ∧
          (0 ≤ p.budget → ∀ trace row,
            (GeneralPaperStoredSelectedLaw.observed model a.address output a.branch trace).output=some row →
            row.size=p.n ∧ FullBudget (p.budget : ℝ) (fun j : Fin p.n => (row.getD j.val 0 : ℝ)) ∧
              ∀ j : Fin p.n,RationalHeight (row.getD j.val 0)
                (GeneralPaperEqualBitDrawRates.word p.n (p.k+1) (rationalWordWidth p.budget))) ∧
          (∫⁻ trace,((GeneralPaperStoredSelectedLaw.observed model a.address output a.branch trace).reads : ℝ≥0∞)
            ∂(traceLaw a.branch : Measure (Trace a.branch))) ≤ (GeneralPaperEqualFirstBitSampling.readsBound p.n p.k : ℝ≥0∞) ∧
          (GeneralPaperEqualInputHeadline.epsilon p<1 → 0<p.budget →
            let μ := GeneralPaperStoredSelectedLaw.outputLaw model a.address output a.branch;
            Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤
              (GeneralPaperEqualInputHeadline.epsilon p : ℝ))) := by
  obtain ⟨K,hK,hSafe⟩ := GeneralPaperFirstStoredCapacity.uniform_capacity model hFast
  obtain ⟨At,et,hTime⟩ := GeneralPaperFirstStoredWork.paper_time model hFast K
  obtain ⟨As,es,hSpace⟩ := GeneralPaperEqualInputHeadline.transfer_rate (GeneralPaperFirstStoredResources.profile_rate model hFast K)
  refine ⟨K,At,et,As,es,hK,fun p => ?_⟩
  obtain ⟨output,hReturn,hWork,hRefines⟩ := GeneralPaperFirstStoredPipeline.source model 1 K p
  have hW : 1 ≤ word K p := Nat.mul_le_mul hK (logarithm_positive p)
  have hDesc := GeneralPaperEqualFirstSelectedDescription.paper_bound model (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualFirstInputPipeline.run model 1 K p).1
  have hMemory := GeneralPaperFirstStoredResident.pipeline_returned model 1 K p output hReturn
  refine ⟨output,hReturn,hWork,?_,?_,GeneralPaperPayloadMemoryOwnership.mono encode _ _ _ hMemory hDesc,?_,?_,?_,?_,?_,?_⟩
  · rw [hWork]
    exact (GeneralPaperFirstStoredWork.work_mono model 1 (word K p) K p hW).trans (hTime p)
  · intro phase
    obtain ⟨keys,hSupport,hBound⟩ := GeneralPaperFirstStoredResources.all_phases model K hK p phase
    have hCap : GeneralPaperFirstStoredResources.profile model K p<2^word K p := by
      have h := hSafe p
      dsimp only [GeneralPaperFirstStoredCapacity.envelope] at h
      omega
    exact ⟨keys,hSupport,hBound.trans (hSpace p),hBound.trans_lt hCap⟩
  · exact GeneralPaperFirstStoredPipeline.law model 1 K p output hReturn
  · exact GeneralPaperEqualFirstSelectedDescription.capacity model (word K p) p.k p.values p.selector p.correct p.budget _
  · exact GeneralPaperStoredSelectedLaw.completed_ae model _ output _ hRefines
  · exact fun hB => GeneralPaperFirstStoredOutput.pipeline_written_output model 1 K p hB output hReturn
  · exact GeneralPaperFirstStoredOutput.pipeline_expected_reads model 1 K p output hReturn
  · exact fun hOne hB => GeneralPaperFirstStoredPipeline.epsilon model 1 K p hOne hB output hReturn

theorem independent_players (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (output : Installed (GeneralPaperFirstStoredPipeline.width model A K p)) :
    let a := (GeneralPaperEqualFirstInputPipeline.run model A K p).1
    let μ := (traceLaw a.branch : Measure (Trace a.branch))
    let f := GeneralPaperStoredSelectedLaw.realDecode model a.address output a.branch
    Measure.map (Prod.map f f) (μ.prod μ)=
      (GeneralPaperStoredSelectedLaw.outputLaw model a.address output a.branch : Measure (Allocation p.n)).prod
        (GeneralPaperStoredSelectedLaw.outputLaw model a.address output a.branch : Measure (Allocation p.n)) :=
  GeneralPaperStoredSelectedLaw.independent_players model _ output _

end Blotto.GeneralPaperFirstStoredContract
