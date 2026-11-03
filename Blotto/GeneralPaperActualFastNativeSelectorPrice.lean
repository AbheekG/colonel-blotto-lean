import Blotto.GeneralPaperFastNativeSelectorPrice

/-! Both complete reached native selectors use the new fast prices.
Classified rich/poor source normalizations discharge the budget-word premise
from actual returned proxy data. No original input-height or tree oracle is
passed to these joins, and no selector execution is repeated. -/
namespace Blotto.GeneralPaperActualFastNativeSelectorPrice
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperFastRationalModel GeneralPaperFastNativeSelectorPrice
open GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def Prices {m k : ℕ} (C d : ℕ) (model : RationalCostModel) (W Qv T : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ) : Prop :=
  (GeneralPaperNativeSelectorExecution.pick true (fun x => x) model.rat W prepared T ready weights prefixes B).2≤
    pickProfile C d W m ready.alphabet.lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2)
      prepared.grid.size prepared.parameters.height prepared.parameters.leafCount

theorem prices_of_checked {m k : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ)
    (hp : prepared=GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
    (hb : rationalWordWidth B≤GeneralPaperTagHeight.word (ready.alphabet.lambda+1) 0)
    (checked : GeneralPaperActualNativeSelectorPrice.Prices model W Qv T prepared ready weights prefixes B) :
    Prices C d model W Qv T prepared ready weights prefixes B := by
  have hn := checked.1
  have hh : prepared.parameters.height=(GeneralPaperProfitParameters.parameters m ready.alphabet.lambda k Qv).height := by rw [hp]; rfl
  have hc : GeneralPaperNativeSelectorPrice.pickProfile model W m ready.alphabet.lambda k Qv
      ((GeneralPaperSourceParameters.prepare k).summarySize+2) prepared.grid.size prepared.parameters.height prepared.parameters.leafCount (rationalWordWidth B)≤
      pickProfile C d W m ready.alphabet.lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size prepared.parameters.height prepared.parameters.leafCount := by
    rw [hh]
    exact pick_profile_bound hg W m ready.alphabet.lambda k Qv _ _ _ _ hb
  exact hn.trans hc

def Both {m k : ℕ} {cache : Cache m k} (C d : ℕ) (model : RationalCostModel) (W Qv : ℕ)
    (current : Run cache) (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) : Prop :=
  Prices C d model W Qv current.T current.profit cache.candidate current.weights (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)) current.Bc ∧
    Prices C d model W Qv current.T current.profit cache.response current.weights (FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)) current.Br

theorem both_work {m k : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W Qv : ℕ) (cache : Cache m k) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (cache.alphabet.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (cache.alphabet.lambda+1) 0) :
    Both C d model W Qv (selected cache Qv weights Bc Br) (beforeAt (selected cache Qv weights Bc Br) time) := by
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have checked := GeneralPaperActualNativeSelectorPrice.both_work model W Qv cache weights Bc Br hw time ht
  exact ⟨prices_of_checked hg W Qv _ _ _ _ _ _ (by rw [hca]; rfl) (by rw [hca]; exact hbc) checked.1,
    prices_of_checked hg W Qv _ _ _ _ _ _ (by rw [hra]; rfl) (by rw [hra]; exact hbr) checked.2⟩

theorem epoch_both_work {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) :
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let current := GeneralPaperCatalogueShared.epochRun shared a k trees
    Both C d model W Qv current (beforeAt current time) := by
  dsimp only
  rw [GeneralPaperCatalogueShared.epochRun_selected]
  exact both_work hg W Qv _ weights Bc Br hw time ht hbc hbr

theorem classified_epoch {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (weights : FixedArrayTable m ℕ)
    (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let a := GeneralPaperProxyParameters.alphabet m k
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    let current := GeneralPaperCatalogueShared.epochRun shared a k (GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch)
    Both C d model W Qv current (beforeAt current time) := by
  apply epoch_both_work hg W k Qv _ weights _ _ hw epoch time ht
  · simpa only [GeneralPaperTagHeight.word_zero,GeneralPaperSourceBudgetWidths.word,GeneralPaperSourceBudgetWidths.height]
      using GeneralPaperSourceBudgetWidths.own_word m k b hb reciprocal
  · simpa only [GeneralPaperTagHeight.word_zero,GeneralPaperSourceBudgetWidths.word,GeneralPaperSourceBudgetWidths.height]
      using GeneralPaperSourceBudgetWidths.opposing_word m k b hb reciprocal

theorem classified_prepared {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (weights : FixedArrayTable m ℕ)
    (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let Bc := ownBudget m k (b:ℝ) reciprocal
    let Br := opposingBudget m k (b:ℝ) reciprocal
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let current := GeneralPaperCatalogueShared.epochRun shared a k (GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch)
    Both C d model W Qv current (beforeAt current time) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact classified_epoch hg W k Qv (b:ℝ) (by exact_mod_cast hb) reciprocal weights hw epoch time ht

end Blotto.GeneralPaperActualFastNativeSelectorPrice
