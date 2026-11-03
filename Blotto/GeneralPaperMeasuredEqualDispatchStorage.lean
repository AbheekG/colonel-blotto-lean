import Blotto.GeneralPaperMeasuredEqualDispatchFrame

/-! Equal preparation includes the outer dispatcher, the retained actual
source and every resident-memory prefix, without repeating initialization. -/
namespace Blotto.GeneralPaperMeasuredEqualDispatchStorage
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open GeneralPaperMeasuredEqualStoragePhases (Phase resident)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

noncomputable def envelope (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  32768 * (GeneralPaperStoredPreparationUniformCapacity.envelope model K p +
    GeneralPaperMixedInitializerPhases.profile model W K p + W + GeneralPaperMeasuredEqualDispatchFrame.branchPrice model p + 1)

noncomputable def window (model : RationalCostModel) (K : ℕ) (p : Input model) (phase : Phase model K p) : ℕ :=
  GeneralPaperMeasuredEqualStoragePhases.window model 1 K p phase + GeneralPaperMeasuredEqualDispatchFrame.window model K p

noncomputable def profile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperMeasuredEqualStoragePhases.profile model K p + GeneralPaperMeasuredEqualDispatchFrame.profile model K p

theorem frame_envelope (model : RationalCostModel) (K : ℕ) (p : Input model) (hK : 1 ≤ K) :
    GeneralPaperMeasuredEqualDispatchFrame.window model K p ≤
      4096 * (GeneralPaperStoredPreparationUniformCapacity.envelope model K p + word K p +
        GeneralPaperMeasuredEqualDispatchFrame.branchPrice model p + 1) := by
  have h := GeneralPaperMeasuredEqualDispatchFrame.window_bound model K p hK
  have hb := GeneralPaperNaturalScalarLifetime.counter_word (GeneralPaperMeasuredEqualDispatchFrame.cap model K p)
  have hc : GeneralPaperPreparationCallerControls.cap model K p ≤
      GeneralPaperStoredPreparationUniformCapacity.envelope model K p := by
    unfold GeneralPaperStoredPreparationUniformCapacity.envelope
    omega
  unfold GeneralPaperMeasuredEqualDispatchFrame.profile GeneralPaperMeasuredEqualDispatchFrame.cap at h hb
  change GeneralPaperEncodedScalarStorage.natBits _ ≤ _ at hb
  omega

theorem all_phases (model : RationalCostModel) (K : ℕ) (p : Input model) (hK : 1 ≤ K) (phase : Phase model K p) :
    ∃ keys : Finset ℕ, (∀ key, resident model 1 K p phase key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys, cellSize encode (resident model 1 K p phase) key) + window model K p phase ≤ profile model K p ∧
      (∑ key ∈ keys, cellSize encode (resident model 1 K p phase) key) + window model K p phase ≤ envelope model (word K p) K p := by
  obtain ⟨keys, hSupport, hSource⟩ := GeneralPaperMeasuredEqualStoragePhases.all_phases model 1 K p hK
    (Nat.mul_le_mul hK (logarithm_positive p)) phase
  have hf := GeneralPaperMeasuredEqualDispatchFrame.window_bound model K p hK
  have he := frame_envelope model K p hK
  have hOld : GeneralPaperStoredPreparationPhases.profile model K p ≤
      GeneralPaperStoredPreparationUniformCapacity.envelope model K p := by
    unfold GeneralPaperStoredPreparationUniformCapacity.envelope
    omega
  refine ⟨keys, hSupport, ?_, ?_⟩
  · dsimp only [window, profile]
    omega
  · dsimp only [window, envelope]
    unfold GeneralPaperMeasuredEqualStoragePhases.profile at hSource
    omega

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (profile model K) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hR : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  have hSource := GeneralPaperMeasuredEqualStoragePhases.profile_rate model hFast K
  have hFrame := at_positive_rate (GeneralPaperMeasuredEqualDispatchFrame.profile_polylog model hFast K) hR
  unfold profile
  fun_prop

theorem paper_space (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) (hK : 1 ≤ K) :
    ∃ C d : ℕ, ∀ (p : Input model) (phase : Phase model K p),
      ∃ keys : Finset ℕ, (∀ key, resident model 1 K p phase key ≠ none → key ∈ keys) ∧
        (∑ key ∈ keys, cellSize encode (resident model 1 K p phase) key) + window model K p phase ≤
          C * GeneralPaperEqualInputHeadline.inputSize p * GeneralPaperEqualInputHeadline.paperLog p ^ d := by
  obtain ⟨C, d, hSize⟩ := GeneralPaperEqualInputHeadline.transfer_rate (profile_rate model hFast K)
  refine ⟨C, d, fun p phase => ?_⟩
  obtain ⟨keys, hSupport, hBound, _⟩ := all_phases model K p hK phase
  exact ⟨keys, hSupport, hBound.trans (hSize p)⟩

end Blotto.GeneralPaperMeasuredEqualDispatchStorage
