import Blotto.GeneralPaperMeasuredEqualHeadlineRates

/-! The measured equal return joins complete enclosing phase storage,
address capacity, time, full returned description and actual sampling law. -/
namespace Blotto.GeneralPaperMeasuredEqualFullContract
open MeasureTheory
open GeneralPaperEqualInputDomain
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open GeneralPaperMeasuredEqualStoragePhases (Phase resident)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

def Independent (model : RationalCostModel) (K : ℕ) (p : Input model)
    (output : Installed (GeneralPaperStoredSelectedPipeline.width model 1 K p)) : Prop :=
  let branch := (GeneralPaperEqualCopiedPipeline.run model 1 K p).1.branch
  let μ := (GeneralPaperEqualBitBranchDraw.traceLaw branch : Measure (GeneralPaperEqualBitBranchDraw.Trace branch))
  let decode := GeneralPaperStoredSelectedLaw.realDecode model
    (GeneralPaperStoredSelectedPipeline.width model 1 K p) output branch
  Measure.map (Prod.map decode decode) (μ.prod μ) =
    (GeneralPaperStoredSelectedLaw.outputLaw model (GeneralPaperStoredSelectedPipeline.width model 1 K p)
      output branch : Measure (Allocation p.n)).prod
    (GeneralPaperStoredSelectedLaw.outputLaw model (GeneralPaperStoredSelectedPipeline.width model 1 K p)
      output branch : Measure (Allocation p.n))

structure Resources (model : RationalCostModel) (K Ct dt Cs ds Cd dd : ℕ)
    (p : GeneralPaperOriginalGameInput.Input)
    (output : Installed (GeneralPaperStoredSelectedPipeline.width model 1 K (GeneralPaperOriginalGameInput.equalInput model p))) : Prop where
  pipeline_returned : (GeneralPaperStoredSelectedPipeline.run model 1 K (GeneralPaperOriginalGameInput.equalInput model p)).1 = some output
  dispatch_returned : (GeneralPaperMeasuredBitDispatch.run model K p).1 = some (.equal _ output)
  computed_word : (GeneralPaperOriginalMeasuredReference.prepare model 1 K p).1.2 =
    word K (GeneralPaperOriginalGameInput.equalInput model p)
  game : GeneralPaperAllBranchBitLaw.Guarantee model K p (.equal _ output)
  pointwise : GeneralPaperAllBranchBitOutput.Pointwise model K p (.equal _ output)
  sampling : GeneralPaperStoredPipelineSamplingContract.Contract model 1 K (GeneralPaperOriginalGameInput.equalInput model p) output
  independent : Independent model K (GeneralPaperOriginalGameInput.equalInput model p) output
  time : (GeneralPaperMeasuredBitDispatch.run model K p).2 ≤
    Ct * GeneralPaperEqualInputHeadline.inputSize (GeneralPaperOriginalGameInput.equalInput model p) *
      GeneralPaperEqualInputHeadline.paperLog (GeneralPaperOriginalGameInput.equalInput model p) ^ dt
  description : ∃ keys : Finset ℕ, (∀ key, output.memory key ≠ none → key ∈ keys) ∧
    (∑ key ∈ keys, cellSize encode output.memory key) +
      GeneralPaperMeasuredEqualHeadlineRates.headBits model K (GeneralPaperOriginalGameInput.equalInput model p) output ≤
        Cd * GeneralPaperEqualInputHeadline.inputSize (GeneralPaperOriginalGameInput.equalInput model p) *
          GeneralPaperEqualInputHeadline.paperLog (GeneralPaperOriginalGameInput.equalInput model p) ^ dd
  space : ∀ phase : Phase model K (GeneralPaperOriginalGameInput.equalInput model p), ∃ keys : Finset ℕ,
    (∀ key, resident model 1 K (GeneralPaperOriginalGameInput.equalInput model p) phase key ≠ none → key ∈ keys) ∧
    (∑ key ∈ keys, cellSize encode (resident model 1 K (GeneralPaperOriginalGameInput.equalInput model p) phase) key) +
      GeneralPaperMeasuredEqualDispatchStorage.window model K (GeneralPaperOriginalGameInput.equalInput model p) phase ≤
        Cs * GeneralPaperEqualInputHeadline.inputSize (GeneralPaperOriginalGameInput.equalInput model p) *
          GeneralPaperEqualInputHeadline.paperLog (GeneralPaperOriginalGameInput.equalInput model p) ^ ds ∧
    (∑ key ∈ keys, cellSize encode (resident model 1 K (GeneralPaperOriginalGameInput.equalInput model p) phase) key) +
      GeneralPaperMeasuredEqualDispatchStorage.window model K (GeneralPaperOriginalGameInput.equalInput model p) phase <
        2 ^ word K (GeneralPaperOriginalGameInput.equalInput model p)

theorem same_return {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ cal : GeneralPaperEnlargedReferenceSourceTime.Reference model C d,
      cal.word = GeneralPaperMeasuredReferenceGrowth.word model K ∧
      GeneralPaperMeasuredJointStorageCalibration.Safe model C d K ∧
      GeneralPaperMeasuredUnequalFullContract.Safe model C d K ∧
      ∃ Ct dt Cs ds Cd dd : ℕ, ∀ p : GeneralPaperOriginalGameInput.Input,
        p.n ≠ 1 → p.budget = 1 → GeneralPaperOriginalGameInput.epsilon p < 1 →
        ∃ output : Installed (GeneralPaperStoredSelectedPipeline.width model 1 K (GeneralPaperOriginalGameInput.equalInput model p)),
          Resources model K Ct dt Cs ds Cd dd p output := by
  have hFast : GeneralPaperFastRationalModel.IsFast model := ⟨C, d, hg⟩
  obtain ⟨K, hK, cal, hWord, hSafe, hNativeSafe⟩ := GeneralPaperMeasuredJointStorageCalibration.calibrated_reference hg
  obtain ⟨Ct, dt, hTime⟩ := GeneralPaperEqualInputHeadline.transfer_rate
    (GeneralPaperMeasuredEqualHeadlineRates.time_rate model hFast K)
  obtain ⟨Cs, ds, hSpace⟩ := GeneralPaperEqualInputHeadline.transfer_rate
    (GeneralPaperMeasuredEqualDispatchStorage.profile_rate model hFast K)
  obtain ⟨Cd, dd, hDescription⟩ := GeneralPaperEqualInputHeadline.transfer_rate
    (GeneralPaperMeasuredEqualHeadlineRates.description_rate model hFast K)
  refine ⟨K, hK, cal, hWord, hSafe, hNativeSafe, Ct, dt, Cs, ds, Cd, dd, fun p hN hB hOne => ?_⟩
  let ep := GeneralPaperOriginalGameInput.equalInput model p
  obtain ⟨output, hMeasured, hPipeline⟩ := GeneralPaperMeasuredEqualPreparation.returns model 1 K p
  have hReturn : (GeneralPaperMeasuredBitDispatch.run model K p).1 = some (.equal _ output) := by
    rw [GeneralPaperMeasuredBitDispatch.on_equal model K p hN hB]
    exact hMeasured
  have hGame := GeneralPaperMeasuredBitDispatch.every_returned model K p hOne (.equal _ output) hReturn
  refine ⟨output, {
    pipeline_returned := hPipeline
    dispatch_returned := hReturn
    computed_word := GeneralPaperOriginalMeasuredReference.word model 1 K p
    game := hGame.1
    pointwise := hGame.2
    sampling := GeneralPaperStoredPipelineSamplingContract.every_returned model 1 K ep output hPipeline
    independent := GeneralPaperStoredPipelineSamplingContract.independent_players model 1 K ep output
    time := ?_
    description := ?_
    space := ?_ }⟩
  · have ht := GeneralPaperMeasuredDispatchResources.equal_work model K hK p hN hB
    change (GeneralPaperMeasuredBitDispatch.run model K p).2 ≤ GeneralPaperMeasuredEqualHeadlineRates.timePrice model K ep at ht
    exact ht.trans (hTime ep)
  · obtain ⟨keys, hSupport, hBound⟩ := GeneralPaperMeasuredEqualHeadlineRates.description_bound model K ep hK output hPipeline
    exact ⟨keys, hSupport, hBound.trans (hDescription ep)⟩
  · intro phase
    obtain ⟨keys, hSupport, hBound, hEnvelope⟩ := GeneralPaperMeasuredEqualDispatchStorage.all_phases model K ep hK phase
    have hCapacity : GeneralPaperMeasuredEqualDispatchStorage.envelope model (word K ep) K ep < 2 ^ word K ep :=
      lt_of_le_of_lt (Nat.le_add_right _ _) (hSafe p)
    exact ⟨keys, hSupport, hBound.trans (hSpace ep), hEnvelope.trans_lt hCapacity⟩

end Blotto.GeneralPaperMeasuredEqualFullContract
