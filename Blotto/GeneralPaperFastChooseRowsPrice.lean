import Blotto.GeneralPaperActualFastNativeSelectorPrice

/-! Join both complete native fast selectors to the actual shared prefix-view
constructor. For classified source budgets the resulting round-choice price
is independent of the original ratio's encoding length. -/
namespace Blotto.GeneralPaperFastChooseRowsPrice
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
open GeneralPaperFastRationalModel GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def profile (C d W m lambda k Qv : ℕ) : ℕ :=
  let p := GeneralPaperProfitParameters.prepare m lambda k Qv
  GeneralPaperRoundPrefixViews.profile W m+
    2*GeneralPaperFastNativeSelectorPrice.pickProfile C d W m lambda k Qv
      ((GeneralPaperSourceParameters.prepare k).summarySize+2) p.grid.size p.parameters.height p.parameters.leafCount+128*W

theorem profile_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv BcWord BrWord : ℕ)
    (hbc : BcWord≤GeneralPaperTagHeight.word (lambda+1) 0)
    (hbr : BrWord≤GeneralPaperTagHeight.word (lambda+1) 0) :
    let p := GeneralPaperProfitParameters.prepare m lambda k Qv
    GeneralPaperChooseRowsPrice.profile model W m lambda k Qv p.grid.size p.parameters.height p.parameters.leafCount BcWord BrWord≤
      profile C d W m lambda k Qv := by
  have hc := GeneralPaperFastNativeSelectorPrice.pick_profile_bound hg W m lambda k Qv
    ((GeneralPaperSourceParameters.prepare k).summarySize+2) (GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size
    (GeneralPaperProfitParameters.prepare m lambda k Qv).parameters.leafCount BcWord hbc
  have hr := GeneralPaperFastNativeSelectorPrice.pick_profile_bound hg W m lambda k Qv
    ((GeneralPaperSourceParameters.prepare k).summarySize+2) (GeneralPaperProfitParameters.prepare m lambda k Qv).grid.size
    (GeneralPaperProfitParameters.prepare m lambda k Qv).parameters.leafCount BrWord hbr
  dsimp only [GeneralPaperChooseRowsPrice.profile,profile,GeneralPaperProfitParameters.prepare] at hc hr ⊢
  omega

theorem selected_work {m k : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W Qv : ℕ) (cache : Cache m k) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (cache.alphabet.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (cache.alphabet.lambda+1) 0) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperChooseRowsExecution.run true (fun x => x) model.rat W cache current.profit current.T weights (beforeAt current time) Bc Br).2≤
      profile C d W m cache.alphabet.lambda k Qv :=
  (GeneralPaperChooseRowsPrice.selected_work model W Qv cache weights Bc Br hw time ht).1.trans
    (profile_bound hg W m cache.alphabet.lambda k Qv _ _ hbc hbr)

theorem epoch_work {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) :
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let cache := GeneralPaperCatalogueShared.cache shared a k trees
    let current := GeneralPaperCatalogueShared.epochRun shared a k trees
    (GeneralPaperChooseRowsExecution.run true (fun x => x) model.rat W cache current.profit current.T weights (beforeAt current time) Bc Br).2≤
      profile C d W m a.lambda k Qv := by
  dsimp only
  rw [GeneralPaperCatalogueShared.epochRun_selected]
  exact selected_work hg W Qv _ weights Bc Br hw time ht hbc hbr

theorem classified_epoch {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (weights : FixedArrayTable m ℕ)
    (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let a := GeneralPaperProxyParameters.alphabet m k
    let Bc := ownBudget m k b reciprocal
    let Br := opposingBudget m k b reciprocal
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let cache := GeneralPaperCatalogueShared.cache shared a k trees
    let current := GeneralPaperCatalogueShared.epochRun shared a k trees
    (GeneralPaperChooseRowsExecution.run true (fun x => x) model.rat W cache current.profit current.T weights (beforeAt current time) Bc Br).2≤
      profile C d W m a.lambda k Qv := by
  apply epoch_work hg W k Qv _ weights _ _ hw epoch time ht
  · simpa only [GeneralPaperTagHeight.word_zero,GeneralPaperSourceBudgetWidths.word,GeneralPaperSourceBudgetWidths.height]
      using GeneralPaperSourceBudgetWidths.own_word m k b hb reciprocal
  · simpa only [GeneralPaperTagHeight.word_zero,GeneralPaperSourceBudgetWidths.word,GeneralPaperSourceBudgetWidths.height]
      using GeneralPaperSourceBudgetWidths.opposing_word m k b hb reciprocal

end Blotto.GeneralPaperFastChooseRowsPrice
