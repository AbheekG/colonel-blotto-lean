import Blotto.GeneralPaperEqualCopyComponentCapacity

/-! Actual initialized copied-pipeline time and all existing preparation,
grouped-copy and pure-row-copy component windows share one fixed coefficient
and sharp paper headline. The selected-copy wrapper/parent and final layout
composition are explicitly outside this component endpoint. -/
namespace Blotto.GeneralPaperEqualCopyComponentContract
open GeneralPaperEqualInputDomain GeneralPaperEqualInputHeadline
open GeneralPaperEqualCopyComponentCapacity (profile)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem paper_time_and_component_windows (model : RationalCostModel)
    (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es : ℕ,1 ≤ K ∧ ∀ p : Input model,
      let W := word K p
      (GeneralPaperEqualCopiedPipeline.run model W K p).2 ≤ At * inputSize p * (paperLog p) ^ et ∧
      (∀ phase : GeneralPaperEqualSelectedPreparationResources.Phase model W p,
        GeneralPaperEqualSelectedPreparationResources.window model W K p phase ≤ As * inputSize p * (paperLog p) ^ es ∧
        GeneralPaperEqualSelectedPreparationResources.window model W K p phase < 2 ^ W) ∧
      (∀ small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded true model W p.k p.values p.selector p.correct).weight j ≤ 1,
        let a := GeneralPaperEqualStoredBitSampler.native true model W p.k p.values p.selector p.correct small p.budget
        ∀ cursor : GeneralPaperEqualNativeCopyLifetime.Cursor a,
          GeneralPaperEqualNativeCopyLifetime.window W a.address a cursor ≤ As * inputSize p * (paperLog p) ^ es ∧
          GeneralPaperEqualNativeCopyLifetime.window W a.address a cursor < 2 ^ W) ∧
      (∀ (chosen : Fin p.n) (source : RationalResourceArray p.n)
        (_correct : source.realAllocation = PureBoundaryEquilibria.vertex (p.budget : ℝ) chosen)
        (j : ℕ) (hj : j ≤ p.n),
        GeneralPaperEqualPureCopyLifetime.window W
          (GeneralPaperEqualBitDrawRates.address p.n 0 p.k (rationalWordWidth p.budget) + 1) source j hj ≤
            As * inputSize p * (paperLog p) ^ es ∧
        GeneralPaperEqualPureCopyLifetime.window W
          (GeneralPaperEqualBitDrawRates.address p.n 0 p.k (rationalWordWidth p.budget) + 1) source j hj < 2 ^ W) := by
  obtain ⟨K,hK,hSafe⟩ := GeneralPaperEqualCopyComponentCapacity.uniform_capacity model hFast
  obtain ⟨At,et,hTime⟩ := GeneralPaperEqualCopiedPipeline.paper_time model hFast K
  obtain ⟨As,es,hSpace⟩ := transfer_rate (GeneralPaperEqualCopyComponentCapacity.profile_rate model hFast K)
  refine ⟨K,At,et,As,es,hK,fun p => ?_⟩
  dsimp only
  refine ⟨hTime p,?_,?_,?_⟩
  · intro phase
    obtain ⟨hW,hIndex⟩ := GeneralPaperEqualDispatchContract.constructed_index_word K hK p
    have h := GeneralPaperEqualSelectedPreparationResources.all_phases model (word K p) K p hW hIndex phase
    have hTotal : GeneralPaperEqualSelectedPreparationResources.window model (word K p) K p phase ≤
        profile model (word K p) K p := by
      dsimp only [profile]
      omega
    exact ⟨hTotal.trans (hSpace p),hTotal.trans_lt (hSafe p)⟩
  · intro small cursor
    have h := GeneralPaperEqualNativeCopyLifetime.native model (word K p) (word K p) p.k
      p.values p.selector p.correct small p.budget cursor
    have hTotal : GeneralPaperEqualNativeCopyLifetime.window (word K p)
        (GeneralPaperEqualStoredBitSampler.native true model (word K p) p.k p.values p.selector p.correct small p.budget).address
        (GeneralPaperEqualStoredBitSampler.native true model (word K p) p.k p.values p.selector p.correct small p.budget) cursor ≤
        profile model (word K p) K p := by
      dsimp only [profile]
      omega
    exact ⟨hTotal.trans (hSpace p),hTotal.trans_lt (hSafe p)⟩
  · intro chosen source correct j hj
    have h := GeneralPaperEqualPureCopyLifetime.all_cursors (word K p) p.k p.budget chosen source correct j hj
    have hTotal : GeneralPaperEqualPureCopyLifetime.window (word K p)
        (GeneralPaperEqualBitDrawRates.address p.n 0 p.k (rationalWordWidth p.budget) + 1) source j hj ≤
        profile model (word K p) K p := by
      dsimp only [profile]
      omega
    exact ⟨hTotal.trans (hSpace p),hTotal.trans_lt (hSafe p)⟩

end Blotto.GeneralPaperEqualCopyComponentContract
