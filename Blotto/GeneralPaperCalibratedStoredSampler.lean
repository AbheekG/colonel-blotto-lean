import Blotto.GeneralPaperStoredPipelineSamplingContract

/-! The globally calibrated preparation and complete common-runtime
sampling contract hold on one actual returned sampler. Preparation time,
working storage and address capacity use one fixed coefficient. Draw work
retains its separate native scale, excluding accuracy encoding length. -/
namespace Blotto.GeneralPaperCalibratedStoredSampler
open MeasureTheory
open scoped ENNReal
open GeneralPaperEqualInputDomain
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open GeneralPaperUniformResourceGrowth
open GeneralPaperStoredPreparationPhases (Phase resident window)
open GeneralPaperEqualBitBranchDraw (Trace traceLaw)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def drawMajorant (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperStoredPipelineDrawWork.majorant model (word K p) K p

theorem draw_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (drawMajorant model K) GeneralPaperStoredSelectedReturnWork.inputScale GeneralPaperStoredNativeReadRates.drawLog := by
  have hSame : drawMajorant model K = GeneralPaperStoredPipelineDrawWork.majorant model 1 K := by
    funext p
    exact GeneralPaperStoredPipelineDrawWork.majorant_independent model (word K p) 1 K p
  rw [hSame]
  exact GeneralPaperStoredPipelineDrawWork.rate model hFast 1 K

theorem calibrated (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
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
      ∃ output : Installed (GeneralPaperStoredSelectedPipeline.width model (word K p) K p),
        (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1 = some output ∧
        output.work = (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).2 ∧
        GeneralPaperStoredPipelineSamplingContract.Contract model (word K p) K p output ∧
        (GeneralPaperEqualInputHeadline.epsilon p < 1 → 0 < p.budget →
          let μ := GeneralPaperStoredSelectedLaw.outputLaw model
            (GeneralPaperStoredSelectedPipeline.width model (word K p) K p) output
            (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1.branch
          Supported (p.budget : ℝ) μ ∧ regret p.selector.values (p.budget : ℝ) μ μ ≤
            (GeneralPaperEqualInputHeadline.epsilon p : ℝ)) := by
  obtain ⟨K,Ct,dt,Cs,ds,hK,hPrepared⟩ :=
    GeneralPaperStoredPreparationPaperContract.time_space_capacity_equilibrium model hFast
  refine ⟨K,Ct,dt,Cs,ds,hK,fun p => ?_⟩
  obtain ⟨hTime,hPrice,hControls,hPhases,_⟩ := hPrepared p
  obtain ⟨output,hReturn,hWork,_⟩ := GeneralPaperStoredSelectedPipeline.source model (word K p) K p
  exact ⟨hTime,hPrice,hControls,hPhases,output,hReturn,hWork,
    GeneralPaperStoredPipelineSamplingContract.every_returned model (word K p) K p output hReturn,
    fun hOne hBudget => GeneralPaperStoredSelectedPipeline.epsilon model (word K p) K p hOne hBudget output hReturn⟩

end Blotto.GeneralPaperCalibratedStoredSampler
