import Blotto.GeneralPaperSelectedInstallationPrefixes
import Blotto.GeneralPaperEqualSelectedPreparationCapacity

/-! One preparation phase family joins the source initializer/dispatch/close,
selected-copy cursors, every native inner/outer write prefix, and the actual
returned RAM. Caller owners and complete stored-construction windows stay
reserved throughout. Uniform address calibration remains a separate join. -/
namespace Blotto.GeneralPaperStoredPreparationPhases
open GeneralPaperEqualInputDomain
open GeneralPaperUnifiedFieldValue (Value Memory encode)
open GeneralPaperPayloadMemoryOwnership (Bounded cellSize)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

inductive Phase (model : RationalCostModel) (K : ℕ) (p : Input model)
  | source (phase : GeneralPaperEqualSelectedPreparationResources.Phase model (word K p) p)
  | copy (cursor : GeneralPaperEqualSelectedCopyComponents.Cursor
      (GeneralPaperEqualSelectedPipeline.run model (word K p) K p).1)
  | constructing (outer scalars : Bool) (depth : ℕ)
  | returned

noncomputable def window (model : RationalCostModel) (K : ℕ) (p : Input model) : Phase model K p → ℕ
  | .source phase => GeneralPaperStoredPreparationCallerLifetime.window model K p +
      GeneralPaperEqualSelectedPreparationResources.window model (word K p) K p phase
  | .copy cursor => GeneralPaperStoredPreparationCallerLifetime.window model K p +
      GeneralPaperEqualSelectedCopyLifetime.window (word K p)
        (GeneralPaperEqualSelectedPipeline.run model (word K p) K p).1 cursor
  | .constructing _ _ _ => GeneralPaperStoredPreparationCallerLifetime.window model K p
  | .returned => GeneralPaperStoredPreparationCallerLifetime.window model K p

def resident (model : RationalCostModel) (K : ℕ) (p : Input model) : Phase model K p → Memory
  | .source _ => GeneralPaperPayloadMemory.empty Value
  | .copy _ => GeneralPaperPayloadMemory.empty Value
  | .constructing outer scalars depth => GeneralPaperSelectedInstallationPrefixes.memory model (word K p)
      (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1 outer scalars depth
  | .returned => (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1.elim
      (GeneralPaperPayloadMemory.empty Value) (fun output => output.memory)

noncomputable def temporaryProfile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualSelectedPreparationResources.profile model (word K p) K p +
    GeneralPaperEqualSelectedCopyLifetime.profile (word K p) p.n p.k (rationalWordWidth p.budget) +
    GeneralPaperStoredPreparationCallerLifetime.profile model K p

noncomputable def profile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1 +
    temporaryProfile model K p

theorem window_bound (model : RationalCostModel) (K : ℕ) (hK : 1 ≤ K) (p : Input model)
    (phase : Phase model K p) : window model K p phase ≤ temporaryProfile model K p := by
  have hStored := GeneralPaperStoredPreparationCallerLifetime.window_bound model K p
  obtain ⟨hW,hIndex⟩ := GeneralPaperEqualDispatchContract.constructed_index_word K hK p
  cases phase with
  | source phase =>
    have hSource := GeneralPaperEqualSelectedPreparationResources.all_phases model (word K p) K p hW hIndex phase
    dsimp only [window,temporaryProfile]
    omega
  | copy cursor =>
    have hCopy := GeneralPaperEqualSelectedCopyLifetime.all_cursors model (word K p) (word K p)
      p.k p.values p.selector p.correct p.budget _ cursor
    dsimp only [window,temporaryProfile]
    omega
  | constructing outer scalars depth =>
    dsimp only [window,temporaryProfile]
    omega
  | returned =>
    dsimp only [window,temporaryProfile]
    omega

theorem resident_bound (model : RationalCostModel) (K : ℕ) (p : Input model) (phase : Phase model K p) :
    Bounded encode (resident model K p phase)
      (GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1) := by
  cases phase with
  | source phase =>
    exact GeneralPaperPayloadMemoryOwnership.mono encode _ _ _
      (GeneralPaperPayloadMemoryOwnership.empty_bounded encode) (Nat.zero_le _)
  | copy cursor =>
    exact GeneralPaperPayloadMemoryOwnership.mono encode _ _ _
      (GeneralPaperPayloadMemoryOwnership.empty_bounded encode) (Nat.zero_le _)
  | constructing outer scalars depth =>
    exact GeneralPaperSelectedInstallationPrefixes.bounded model (word K p) _ outer scalars depth
  | returned =>
    dsimp only [resident]
    cases hReturn : (GeneralPaperStoredSelectedPipeline.run model (word K p) K p).1 with
    | none =>
      exact GeneralPaperPayloadMemoryOwnership.mono encode _ _ _
        (GeneralPaperPayloadMemoryOwnership.empty_bounded encode) (Nat.zero_le _)
    | some output =>
      exact GeneralPaperStoredConstructorMemoryOwnership.pipeline_returned model (word K p) K p output hReturn

theorem all_phases (model : RationalCostModel) (K : ℕ) (hK : 1 ≤ K) (p : Input model) (phase : Phase model K p) :
    ∃ keys : Finset ℕ,(∀ key,resident model K p phase key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode (resident model K p phase) key) + window model K p phase ≤ profile model K p := by
  obtain ⟨keys,hSupport,hResident⟩ := resident_bound model K p phase
  exact ⟨keys,hSupport,Nat.add_le_add hResident (window_bound model K hK p phase)⟩

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (profile model K) ledger logarithm := by
  have hSource := GeneralPaperEqualSelectedPreparationCapacity.profile_rate model hFast K
  have hCopy := GeneralPaperEqualSelectedCopyLifetimeRates.profile_rate model K
  have hStored := GeneralPaperStoredPreparationCallerLifetime.profile_rate model hFast K
  have hDescription := GeneralPaperSelectedPreparationInputRates.description_rate model K (word K)
  exact bound_add _ _ ledger logarithm logarithm_positive hDescription
    (bound_add _ _ ledger logarithm logarithm_positive
      (bound_add _ _ ledger logarithm logarithm_positive hSource hCopy) hStored)

theorem paper_peak (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) (hK : 1 ≤ K) :
    ∃ C d : ℕ,∀ (p : Input model) (phase : Phase model K p),
      ∃ keys : Finset ℕ,(∀ key,resident model K p phase key ≠ none → key ∈ keys) ∧
        (∑ key ∈ keys,cellSize encode (resident model K p phase) key) + window model K p phase ≤
          C * GeneralPaperEqualInputHeadline.inputSize p * GeneralPaperEqualInputHeadline.paperLog p ^ d := by
  obtain ⟨C,d,hSize⟩ := GeneralPaperEqualInputHeadline.transfer_rate (profile_rate model hFast K)
  refine ⟨C,d,fun p phase => ?_⟩
  obtain ⟨keys,hSupport,hBound⟩ := all_phases model K hK p phase
  exact ⟨keys,hSupport,hBound.trans (hSize p)⟩

end Blotto.GeneralPaperStoredPreparationPhases
