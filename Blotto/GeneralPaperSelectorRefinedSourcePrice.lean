import Blotto.GeneralPaperFastChooseRowsPrice

/-! Refine the complete native source price with the complete fast selector
bound, using constructed source-budget words. Non-selector components keep
their explicit existing Rat prices. This is a bound on the actual full run,
not a replacement by a DP-only component sum. No algorithm pass is added. -/
namespace Blotto.GeneralPaperSelectorRefinedSourcePrice
open GeneralPaperFastRationalModel GeneralPaperCodeAlphabet
open GeneralPaperInitializerPreparedPoint
open GeneralPaperSummaryArrayExecution (arrayWord)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def roundProfile (model : RationalCostModel) (C d W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperEpochSnapshotFamilyPrice.profile model.rat W m lambda k Qv+
    GeneralPaperFastChooseRowsPrice.profile C d W m lambda k Qv+
    GeneralPaperRoundFieldsPrice.profile model.rat W m lambda k Qv+
    2*GeneralPaperSelectedRowCodesPrice.profile W m ((GeneralPaperSourceParameters.prepare k).summarySize+2) lambda+256*W

theorem round_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv BcWord BrWord : ℕ)
    (hbc : BcWord≤GeneralPaperTagHeight.word (lambda+1) 0)
    (hbr : BrWord≤GeneralPaperTagHeight.word (lambda+1) 0) :
    let p := GeneralPaperProfitParameters.prepare m lambda k Qv
    GeneralPaperRoundPrice.profile model W m lambda k Qv p.grid.size p.parameters.height p.parameters.leafCount BcWord BrWord≤
      roundProfile model C d W m lambda k Qv :=
  Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (GeneralPaperFastChooseRowsPrice.profile_bound hg W m lambda k Qv BcWord BrWord hbc hbr) _) _) _) _

def localProfile (model : RationalCostModel) (C d W m lambda k Qv count : ℕ) : ℕ :=
  let P := (GeneralPaperTrajectoryParameters.prepare lambda k).period
  GeneralPaperEpochInitialFamilyPrice.profile model.rat W m k+
    (count*(roundProfile model C d W m lambda k Qv+256*arrayWord W (P+2))+256*arrayWord W (P+2))+128*W

theorem local_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv BcWord BrWord count : ℕ)
    (hbc : BcWord≤GeneralPaperTagHeight.word (lambda+1) 0)
    (hbr : BrWord≤GeneralPaperTagHeight.word (lambda+1) 0) :
    let p := GeneralPaperProfitParameters.prepare m lambda k Qv
    GeneralPaperLocalEpochPrice.profile model W m lambda k Qv p.grid.size p.parameters.height p.parameters.leafCount BcWord BrWord count≤
      localProfile model C d W m lambda k Qv count :=
  Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right
    (Nat.mul_le_mul_left count (Nat.add_le_add_right (round_bound hg W m lambda k Qv BcWord BrWord hbc hbr) _)) _) _) _

def outerProfile (model : RationalCostModel) (C d W m k Qv : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperTreeEpochPreparation.profile model W m k Qv a+
    (localProfile model C d W m a.lambda k Qv (GeneralPaperTrajectoryParameters.prepare a.lambda k).period+
      GeneralPaperForestUpdatePrice.profile model.rat W m a.lambda k Qv+256*W)+128*W

theorem outer_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m k Qv : ℕ) (a : Alphabet) (Bc Br : ℚ)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) :
    GeneralPaperOuterEpochPrice.profile model W m k Qv a Bc Br≤outerProfile model C d W m k Qv a :=
  Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_right
    (local_bound hg W m a.lambda k Qv _ _ _ hbc hbr) _) _) _) _

def stepProfile (model : RationalCostModel) (C d W m k Qv : ℕ) (a : Alphabet) : ℕ :=
  let t := GeneralPaperTrajectoryParameters.prepare a.lambda k
  outerProfile model C d W m k Qv a+GeneralPaperTrajectoryAppendPrice.profile W t.rows t.period+256*arrayWord W (t.epochs+2)

theorem step_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m k Qv : ℕ) (a : Alphabet) (Bc Br : ℚ)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) :
    GeneralPaperGeometricSourceStepPrice.profile model W m k Qv a Bc Br≤stepProfile model C d W m k Qv a :=
  Nat.add_le_add_right (Nat.add_le_add_right (outer_bound hg W m k Qv a Bc Br hbc hbr) _) _

def profile (model : RationalCostModel) (C d W m k Qv : ℕ) (a : Alphabet) (count : ℕ) : ℕ :=
  GeneralPaperGeometricSourcePrice.initialProfile W m a.lambda k+count*stepProfile model C d W m k Qv a

theorem profile_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m k Qv : ℕ) (a : Alphabet) (Bc Br : ℚ) (count : ℕ)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) :
    GeneralPaperGeometricSourcePrice.profile model W m k Qv a Bc Br count≤profile model C d W m k Qv a count :=
  Nat.add_le_add_left (Nat.mul_le_mul_left count (step_bound hg W m k Qv a Bc Br hbc hbr)) _

theorem native_work {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) :
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
    (GeneralPaperGeometricSourceExecution.run true (fun x => x) model W k Qv a c hc shared count).2≤profile model C d W m k Qv a count :=
  (GeneralPaperGeometricSourcePrice.work model W k Qv a c hc weights Bc Br hw count he).1.trans
    (profile_bound hg W m k Qv a Bc Br count hbc hbr)

theorem classified_work {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv)
    (weights : FixedArrayTable m ℕ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let a := GeneralPaperProxyParameters.alphabet m k
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (GeneralPaperGeometricSourceExecution.run true (fun x => x) model W k Qv a c hc shared count).2≤profile model C d W m k Qv a count := by
  apply native_work hg W k Qv _ c hc weights _ _ hw count he
  · simpa only [GeneralPaperTagHeight.word_zero,GeneralPaperSourceBudgetWidths.word,GeneralPaperSourceBudgetWidths.height]
      using GeneralPaperSourceBudgetWidths.own_word m k b hb reciprocal
  · simpa only [GeneralPaperTagHeight.word_zero,GeneralPaperSourceBudgetWidths.word,GeneralPaperSourceBudgetWidths.height]
      using GeneralPaperSourceBudgetWidths.opposing_word m k b hb reciprocal

theorem classified_prepared {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (weights : FixedArrayTable m ℕ)
    (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let Bc := ownBudget m k (b:ℝ) reciprocal
    let Br := opposingBudget m k (b:ℝ) reciprocal
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let c := ready.2.source
    let hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
      dsimp only [c,a,ready]
      rw [GeneralPaperPreparedSharedSource.data]
      rfl
    (GeneralPaperGeometricSourceExecution.run true (fun x => x) model W k Qv a c hc ready.1.2 count).2≤
      profile model C d W m k Qv a count := by
  let Bc := ownBudget m k (b:ℝ) reciprocal
  let Br := opposingBudget m k (b:ℝ) reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
  let a := ready.1.1.1.2
  let c := ready.2.source
  have ha : a=GeneralPaperProxyParameters.alphabet m k := by dsimp only [a,ready]; rw [GeneralPaperPreparedSharedSource.data]
  have hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
    dsimp only [c,a,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  have hs : ready.1.2=GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br := by
    dsimp only [ready,a]
    rw [GeneralPaperPreparedSharedSource.data]
  have he' : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs := by rw [ha]; exact he
  have hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0 := by
    rw [ha,GeneralPaperTagHeight.word_zero]
    exact GeneralPaperSourceBudgetWidths.own_word m k (b:ℝ) (by exact_mod_cast hb) reciprocal
  have hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0 := by
    rw [ha,GeneralPaperTagHeight.word_zero]
    exact GeneralPaperSourceBudgetWidths.opposing_word m k (b:ℝ) (by exact_mod_cast hb) reciprocal
  have hn := native_work hg W k Qv a c hc weights Bc Br hw count he' hbc hbr
  dsimp only
  change (GeneralPaperGeometricSourceExecution.run true (fun x => x) model W k Qv a c hc ready.1.2 count).2≤_
  rw [hs]
  exact hn

end Blotto.GeneralPaperSelectorRefinedSourcePrice
