import Blotto.GeneralPaperFirstStoredCaller

/-! All direct corrected stored-preparation phases share one sharp working
bit bound: actual one-pass initialization/source, enclosing callers, every
inner/outer directory/scalar write prefix and the returned resident RAM. -/
namespace Blotto.GeneralPaperFirstStoredResources
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperUnifiedFieldValue (Value Memory encode)
open GeneralPaperPayloadMemoryOwnership (Bounded cellSize)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem caller_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (GeneralPaperFirstStoredCaller.profile model K) ledger logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model,1 ≤ ledger p := GeneralPaperEqualInputDomain.ledger_positive
  have hLedger : Small (ledger (model := model)) logarithm := below_ledger_small _ (fun _ => le_rfl)
  have hSource := GeneralPaperEqualFirstInputCapacity.profile_rate model hFast K
  have hPrice := bound_small hL (GeneralPaperFirstStoredWork.price_rate model hFast K) hLedger
  have hAddress := GeneralPaperFirstStoredRates.address_tight model K (fun _ => 1)
  have hAddressSmall := small_of_tight hAddress hL
  have hAddressRaw : Small (fun p : Input model => (GeneralPaperEqualFirstInputPipeline.run model 1 K p).1.address) logarithm := hAddressSmall
  have hWSmall := small_of_tight (word_tight K model) hL
  have hK := small_constant K logarithm hL
  have hCap : Small (GeneralPaperFirstStoredCaller.cap model K) logarithm := by
    unfold GeneralPaperFirstStoredCaller.cap GeneralPaperFirstStoredCaller.source
    fun_prop
  have hResult := GeneralPaperMeasuredPlanLifetimeRates.unit_rate model hFast (word K)
    (fun p : Input model => (GeneralPaperFirstStoredCaller.source model K p).1.address)
    (GeneralPaperFirstStoredWork.price model K) logarithm hL (word_tight K model) hAddress hPrice
  have hResultRate := rate_mono hResult hr
  have hExtent := GeneralPaperFirstStoredRates.description_rate model K (fun _ => 1)
  have hComponents := GeneralPaperSelectedPreparationGenericRates.combined_rate model hFast (word K) ledger logarithm
    (fun p : Input model => p.n) (fun p => p.k)
    (fun p => GeneralPaperEqualFirstNativeFacts.rounded true model (word K p) p.k p.values p.selector p.correct)
    (fun p => p.budget) (fun p => (GeneralPaperFirstStoredCaller.source model K p).1)
    hL hr (word_tight K model) hAddress hExtent hLedger
    (fun p => GeneralPaperEqualFirstMeasuredLayout.inner_capacity model (word K p) (word K p) p.k
      p.values p.selector p.correct p.budget _)
    (fun p => by
      have h := GeneralPaperEqualFirstMeasuredLayout.total_capacity model (word K p) (word K p) p.k
        p.values p.selector p.correct p.budget (GeneralPaperFirstStoredCaller.source model K p).1
      omega)
  unfold GeneralPaperFirstStoredCaller.profile GeneralPaperFirstStoredCaller.sourceProfile
    GeneralPaperFirstStoredCaller.controlProfile GeneralPaperFirstStoredCaller.resultProfile
  dsimp only [GeneralPaperEqualBitDrawRates.log,GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
  fun_prop (config := {maxSteps := 50000})

inductive Phase (model : RationalCostModel) (K : ℕ) (p : Input model)
  | source (phase : GeneralPaperEqualFirstInputResources.Phase model (word K p) p)
  | constructing (outer scalars : Bool) (depth : ℕ)
  | returned

noncomputable def window (model : RationalCostModel) (K : ℕ) (p : Input model) : Phase model K p → ℕ
  | .source phase => GeneralPaperFirstStoredCaller.window model K p+
      GeneralPaperEqualFirstInputResources.window model (word K p) 1 K p phase
  | .constructing _ _ _ => GeneralPaperFirstStoredCaller.window model K p
  | .returned => GeneralPaperFirstStoredCaller.window model K p

def resident (model : RationalCostModel) (K : ℕ) (p : Input model) : Phase model K p → Memory
  | .source _ => GeneralPaperPayloadMemory.empty Value
  | .constructing outer scalars depth => GeneralPaperSelectedInstallationPrefixes.memory model (word K p)
      (GeneralPaperFirstStoredCaller.source model K p).1 outer scalars depth
  | .returned => (GeneralPaperFirstStoredPipeline.run model 1 K p).1.elim
      (GeneralPaperPayloadMemory.empty Value) (fun output => output.memory)

noncomputable def temporaryProfile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualFirstInputResources.profile model (word K p) K p+GeneralPaperFirstStoredCaller.profile model K p

noncomputable def profile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualSelectedDescription.footprint (GeneralPaperFirstStoredCaller.source model K p).1+
    temporaryProfile model K p

theorem window_bound (model : RationalCostModel) (K : ℕ) (hK : 1 ≤ K) (p : Input model) (phase : Phase model K p) :
    window model K p phase ≤ temporaryProfile model K p := by
  obtain ⟨hW,hIndex⟩ := GeneralPaperEqualDispatchContract.constructed_index_word K hK p
  have hCaller := GeneralPaperFirstStoredCaller.all_components model K p hW
  cases phase with
  | source phase =>
    have hSource := GeneralPaperEqualFirstInputResources.all_phases model (word K p) 1 K p hW hIndex hW phase
    dsimp only [window,temporaryProfile]; omega
  | _ => dsimp only [window,temporaryProfile]; all_goals omega

theorem resident_bound (model : RationalCostModel) (K : ℕ) (p : Input model) (phase : Phase model K p) :
    Bounded encode (resident model K p phase)
      (GeneralPaperEqualSelectedDescription.footprint (GeneralPaperFirstStoredCaller.source model K p).1) := by
  cases phase with
  | source phase =>
    exact GeneralPaperPayloadMemoryOwnership.mono encode _ _ _
      (GeneralPaperPayloadMemoryOwnership.empty_bounded encode) (Nat.zero_le _)
  | constructing outer scalars depth => exact GeneralPaperSelectedInstallationPrefixes.bounded model (word K p) _ outer scalars depth
  | returned =>
    dsimp only [resident]
    cases hReturn : (GeneralPaperFirstStoredPipeline.run model 1 K p).1 with
    | none =>
      exact GeneralPaperPayloadMemoryOwnership.mono encode _ _ _
        (GeneralPaperPayloadMemoryOwnership.empty_bounded encode) (Nat.zero_le _)
    | some output => exact GeneralPaperFirstStoredResident.pipeline_returned model 1 K p output hReturn

theorem all_phases (model : RationalCostModel) (K : ℕ) (hK : 1 ≤ K) (p : Input model) (phase : Phase model K p) :
    ∃ keys : Finset ℕ,(∀ key,resident model K p phase key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode (resident model K p phase) key)+window model K p phase ≤ profile model K p := by
  obtain ⟨keys,hSupport,hResident⟩ := resident_bound model K p phase
  exact ⟨keys,hSupport,Nat.add_le_add hResident (window_bound model K hK p phase)⟩

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (profile model K) ledger logarithm :=
  bound_add _ _ ledger logarithm logarithm_positive
    (GeneralPaperFirstStoredRates.description_rate model K (fun _ => 1))
    (bound_add _ _ ledger logarithm logarithm_positive
      (GeneralPaperEqualFirstInputCapacity.profile_rate model hFast K) (caller_rate model hFast K))

theorem paper_peak (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) (hK : 1 ≤ K) :
    ∃ C d : ℕ,∀ (p : Input model) (phase : Phase model K p),
      ∃ keys : Finset ℕ,(∀ key,resident model K p phase key ≠ none → key ∈ keys) ∧
        (∑ key ∈ keys,cellSize encode (resident model K p phase) key)+window model K p phase ≤
          C*GeneralPaperEqualInputHeadline.inputSize p*(GeneralPaperEqualInputHeadline.paperLog p)^d := by
  obtain ⟨C,d,hSize⟩ := GeneralPaperEqualInputHeadline.transfer_rate (profile_rate model hFast K)
  refine ⟨C,d,fun p phase => ?_⟩
  obtain ⟨keys,hSupport,hBound⟩ := all_phases model K hK p phase
  exact ⟨keys,hSupport,hBound.trans (hSize p)⟩

end Blotto.GeneralPaperFirstStoredResources
