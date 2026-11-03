import Blotto.GeneralPaperEqualDispatchCapacity

/-! The calibrated unrestricted return has sharp paper preparation time,
every joined dispatch phase has sharp working space and common capacity,
and the same returned branch is an original continuous epsilon equilibrium.
Selected draw pricing and preparation/draw address scheduling are separate. -/
namespace Blotto.GeneralPaperEqualDispatchContract
open GeneralPaperEqualInputDomain GeneralPaperEqualDispatchLifetime
open GeneralPaperEqualInputHeadline
open GeneralPaperEqualBitBranch (outputLaw)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

theorem constructed_index_word {model : RationalCostModel} (K : ℕ) (hK : 1 ≤ K) (p : Input model) :
    1 ≤ word K p ∧ binaryWordWidth (p.n + 1) ≤ word K p := by
  have hL := logarithm_positive p
  have hBase : logarithm p ≤ word K p := by unfold word; nlinarith only [hK]
  have hn : p.n + 1 ≤ ledger p := by unfold ledger; omega
  have hw := binaryWordWidth_mono hn
  dsimp only [logarithm] at hBase
  exact ⟨hL.trans (by dsimp only [logarithm]; exact hBase), by omega⟩

theorem selected_grouped (model : RationalCostModel) (W : ℕ) (p : Input model)
    (hNone : (GeneralPaperEqualBitBoundaryScan.run model W (lengths model W p)).1 = none) :
    SmallBranch model p := by
  let r := GeneralPaperEqualNativeSampler.rounded true model W p.k p.values p.selector p.correct
  have hL : ∀ j, (lengths model W p).read j = 2 * r.weight j := by
    intro j
    rw [lengths, GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]
    rfl
  have hReal : (GeneralPaperEqualRealBoundaryScan.run (lengths model W p)).1 = none :=
    (GeneralPaperEqualBitBoundaryScan.run_data model W (lengths model W p)).symm.trans hNone
  have hs := GeneralPaperEqualRealBoundaryScan.none_small (lengths model W p) r hL hReal
  dsimp only [r] at hs
  rw [GeneralPaperEqualResourceDomain.rounded_reference] at hs
  exact hs

theorem all_phase_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (p : Input model) (phase : Phase model (word K p) p),
      window model (word K p) K p phase < 2 ^ word K p := by
  obtain ⟨K,hK,hSafe⟩ := GeneralPaperEqualDispatchCapacity.uniform_capacity model hFast
  refine ⟨K,hK,fun p phase => ?_⟩
  obtain ⟨hW,hIndex⟩ := constructed_index_word K hK p
  exact (all_phases model _ K p hW hIndex phase).trans_lt (hSafe p)

theorem paper_time_space_capacity_and_equilibrium (model : RationalCostModel)
    (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es : ℕ, 1 ≤ K ∧ ∀ p : Input model,
      let W := word K p
      let result := GeneralPaperEqualInputPipeline.run model W K p
      result.2 ≤ At * inputSize p * (paperLog p) ^ et ∧
      (∀ phase : Phase model W p,
        window model W K p phase ≤ As * inputSize p * (paperLog p) ^ es ∧
        window model W K p phase < 2 ^ W) ∧
      (epsilon p < 1 → 0 < p.budget →
        Supported (p.budget : ℝ) (outputLaw model result.1) ∧
        regret p.selector.values (p.budget : ℝ) (outputLaw model result.1) (outputLaw model result.1) ≤
          (epsilon p : ℝ)) := by
  obtain ⟨K,hK,hSafe⟩ := GeneralPaperEqualDispatchCapacity.uniform_capacity model hFast
  obtain ⟨At,et,hTime⟩ := GeneralPaperEqualInputPipeline.paper_time model hFast K
  obtain ⟨As,es,hSpace⟩ := transfer_rate (GeneralPaperEqualDispatchCapacity.profile_rate model hFast K)
  refine ⟨K,At,et,As,es,hK,fun p => ?_⟩
  refine ⟨hTime p,?_,fun hOne hB => GeneralPaperEqualInputPipeline.epsilon model _ K p hOne hB⟩
  intro phase
  obtain ⟨hW,hIndex⟩ := constructed_index_word K hK p
  have hs := all_phases model _ K p hW hIndex phase
  exact ⟨hs.trans (hSpace p),hs.trans_lt (hSafe p)⟩

end Blotto.GeneralPaperEqualDispatchContract
