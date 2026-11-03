import Blotto.GeneralPaperMeasuredEqualCallerStorage

/-! Actual equal preparation phases after initializer repricing. Resident
memory is unchanged; actual caller prices and parsed references are counted.
Canonical cursor types are erased data-equality views of the actual source. -/
namespace Blotto.GeneralPaperMeasuredEqualStoragePhases
open GeneralPaperEqualInputDomain
open GeneralPaperUnifiedFieldValue (Memory Value encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open GeneralPaperUniformResourceGrowth
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

abbrev Phase (model : RationalCostModel) (K : ℕ) (p : Input model) := GeneralPaperStoredPreparationPhases.Phase model K p

noncomputable def window (model : RationalCostModel) (A K : ℕ) (p : Input model) : Phase model K p → ℕ
  | .source phase => GeneralPaperMeasuredEqualCallerStorage.window model A K p +
      GeneralPaperMeasuredEqualSourceStorage.window model (word K p) A K p phase
  | .copy cursor => GeneralPaperMeasuredEqualCallerStorage.window model A K p +
      GeneralPaperEqualSelectedCopyLifetime.window (word K p) (GeneralPaperEqualSelectedPipeline.run model (word K p) K p).1 cursor
  | .constructing _ _ _ => GeneralPaperMeasuredEqualCallerStorage.window model A K p
  | .returned => GeneralPaperMeasuredEqualCallerStorage.window model A K p

def resident (model : RationalCostModel) (A K : ℕ) (p : Input model) : Phase model K p → Memory
  | .source _ => GeneralPaperPayloadMemory.empty Value
  | .copy _ => GeneralPaperPayloadMemory.empty Value
  | .constructing outer scalars depth => GeneralPaperSelectedInstallationPrefixes.memory model (word K p)
      (GeneralPaperEqualCopiedPipeline.run model A K p).1 outer scalars depth
  | .returned => GeneralPaperMeasuredEqualRepricing.memory model A K p

theorem resident_eq (model : RationalCostModel) (A K : ℕ) (p : Input model) (phase : Phase model K p) :
    resident model A K p phase = GeneralPaperStoredPreparationPhases.resident model K p phase := by
  cases phase with
  | source phase => rfl
  | copy cursor => rfl
  | constructing outer scalars depth =>
    dsimp only [resident, GeneralPaperStoredPreparationPhases.resident]
    rw [GeneralPaperMeasuredEqualRepricing.copied_data model A (word K p) K p]
  | returned => exact GeneralPaperMeasuredEqualRepricing.memory_reprice model A (word K p) K p

theorem window_le (model : RationalCostModel) (A K : ℕ) (p : Input model) (h : A ≤ word K p)
    (phase : Phase model K p) :
    window model A K p phase ≤ GeneralPaperStoredPreparationPhases.window model K p phase +
      2 * GeneralPaperMixedInitializerPhases.profile model (word K p) K p + 2 * word K p := by
  have hc := GeneralPaperMeasuredEqualCallerStorage.window_le model A K p h
  cases phase with
  | source phase =>
    have hs := GeneralPaperMeasuredEqualSourceStorage.window_le model (word K p) A K h p phase
    dsimp only [window, GeneralPaperStoredPreparationPhases.window]
    omega
  | _ =>
    dsimp only [window, GeneralPaperStoredPreparationPhases.window]
    all_goals omega

noncomputable def profile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperStoredPreparationPhases.profile model K p +
    2 * GeneralPaperMixedInitializerPhases.profile model (word K p) K p + 2 * word K p

theorem all_phases (model : RationalCostModel) (A K : ℕ) (p : Input model) (hK : 1 ≤ K) (h : A ≤ word K p)
    (phase : Phase model K p) :
    ∃ keys : Finset ℕ, (∀ key, resident model A K p phase key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys, cellSize encode (resident model A K p phase) key) + window model A K p phase ≤ profile model K p := by
  obtain ⟨keys, hSupport, hOld⟩ := GeneralPaperStoredPreparationPhases.all_phases model K hK p phase
  have hNew := window_le model A K p h phase
  refine ⟨keys, ?_, ?_⟩
  · rw [resident_eq]
    exact hSupport
  · rw [resident_eq]
    unfold profile
    omega

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (profile model K) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hR : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  have hOld := GeneralPaperStoredPreparationPhases.profile_rate model hFast K
  have hMixed := GeneralPaperMixedInitializerCalibration.profile_rate model hFast K
  have hWord := polylog_of_tight (word_tight K model)
  unfold profile
  fun_prop

theorem paper_space (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) (hK : 1 ≤ K) :
    ∃ C d : ℕ, ∀ (p : Input model) (phase : Phase model K p),
      ∃ keys : Finset ℕ, (∀ key, resident model 1 K p phase key ≠ none → key ∈ keys) ∧
        (∑ key ∈ keys, cellSize encode (resident model 1 K p phase) key) + window model 1 K p phase ≤
          C * GeneralPaperEqualInputHeadline.inputSize p * GeneralPaperEqualInputHeadline.paperLog p ^ d := by
  obtain ⟨C, d, hSize⟩ := GeneralPaperEqualInputHeadline.transfer_rate (profile_rate model hFast K)
  refine ⟨C, d, fun p phase => ?_⟩
  obtain ⟨keys, hSupport, hBound⟩ := all_phases model 1 K p hK
    (Nat.mul_le_mul hK (logarithm_positive p)) phase
  exact ⟨keys, hSupport, hBound.trans (hSize p)⟩

end Blotto.GeneralPaperMeasuredEqualStoragePhases
