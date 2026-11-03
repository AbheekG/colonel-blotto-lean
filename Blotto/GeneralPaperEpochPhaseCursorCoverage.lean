import Blotto.GeneralPaperRoundPhaseCursorCoverage

/-! Native epoch parents and their produced Ready/field children are
members of the closed epoch frontier. Summary/rank Fin types remain those
of the retained cache; no transport rewrites native dependent indices.
All four learners and both Ready modes are covered. -/
namespace Blotto.GeneralPaperEpochPhaseCursorCoverage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperFiniteStorageWindows GeneralPaperStorageCursorPacking
open GeneralPaperCatalogueOccurrenceHistory (Learner)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def learnerIndex : Learner → Fin 4
  | .p => 0
  | .q => 1
  | .lambda => 2
  | .mu => 3

theorem learner_identity (which : Learner) : GeneralPaperEpochSourcePhaseStorage.learner (learnerIndex which)=which := by
  cases which <;> rfl

theorem parent_point {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count inner row tailCount : ℕ)
    (hcount : count≤m) (hi : inner≤c.controls.source.summarySize)
    (hr : row≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (remaining : Fin (GeneralPaperBatchCounterPrice.limit k+2))
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1))
    (r : Fin c.controls.source.summarySize) (which : Learner) :
    GeneralPaperActualEpochParentStorage.window model W k Qv a c hc weights Bc Br epoch count inner row tailCount remaining.val
      hcount hi hr ht j i q r which≤GeneralPaperEpochSourcePhaseStorage.parents model W k Qv a c hc weights Bc Br epoch := by
  let cursor : GeneralPaperEpochSourcePhaseStorage.ParentCursor m a.lambda k Qv c :=
    (counter m count hcount,counter c.controls.source.summarySize inner hi,
      counter ((GeneralPaperSourceParameters.prepare k).summarySize+2) row hr,
      counter (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1) tailCount ht,
      counter (GeneralPaperRoundPhaseStorage.progressCap m a.lambda k Qv) remaining.val
        (GeneralPaperRoundPhaseCursorCoverage.inner_cap m a.lambda k Qv remaining),j,i,q,r,learnerIndex which)
  have h := observed_le_maximum (GeneralPaperEpochSourcePhaseStorage.parentWindow model W k Qv a c hc weights Bc Br epoch) cursor
  have heq : GeneralPaperEpochSourcePhaseStorage.parentWindow model W k Qv a c hc weights Bc Br epoch cursor=
      GeneralPaperActualEpochParentStorage.window model W k Qv a c hc weights Bc Br epoch count inner row tailCount remaining.val
        hcount hi hr ht j i q r which := by
    dsimp only [GeneralPaperEpochSourcePhaseStorage.parentWindow,cursor,counter]
    exact congrArg (fun which' => GeneralPaperActualEpochParentStorage.window model W k Qv a c hc weights Bc Br epoch
      count inner row tailCount remaining.val hcount hi hr ht j i q r which') (learner_identity which)
  exact heq ▸ h

theorem parents_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    GeneralPaperEpochSourcePhaseStorage.parents model W k Qv a c hc weights Bc Br epoch≤
      GeneralPaperEpochSourcePhaseStorage.window model W k Qv a c hc weights Bc Br epoch := by
  dsimp only [GeneralPaperEpochSourcePhaseStorage.window]
  omega

theorem cache_children_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    GeneralPaperEpochSourcePhaseStorage.cacheChildren model W k Qv a c hc weights Bc Br epoch≤
      GeneralPaperEpochSourcePhaseStorage.window model W k Qv a c hc weights Bc Br epoch := by
  have h := Nat.le_max_left (GeneralPaperEpochSourcePhaseStorage.cacheChildren model W k Qv a c hc weights Bc Br epoch)
    (GeneralPaperLocalSourceLifetimeStorage.window model W k Qv a c weights Bc Br epoch (GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  dsimp only [GeneralPaperEpochSourcePhaseStorage.window]
  omega

theorem field_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let x := GeneralPaperTreeEpochConstructionStorage.arrays model W m k Qv a c hc (GeneralPaperQuantileComparison.width a.lambda k) trees
    let hm := GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc
    GeneralPaperFieldPreparationPhaseStorage.peak model W a x
      (GeneralPaperEpochCacheConstructionStorage.candidate model W c.controls.source.meshDenominator a x hm).data.codes
      (GeneralPaperEpochCacheConstructionStorage.response model W c.controls.source.meshDenominator a x hm).data.codes≤
        GeneralPaperEpochSourcePhaseStorage.window model W k Qv a c hc weights Bc Br epoch :=
  (Nat.le_max_right ..).trans (cache_children_covered model W k Qv a c hc weights Bc Br epoch)

theorem ready_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (response : Bool) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let x := GeneralPaperTreeEpochConstructionStorage.arrays model W m k Qv a c hc (GeneralPaperQuantileComparison.width a.lambda k) trees
    let hm := GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc
    GeneralPaperReadyPreparationPhaseStorage.peak model W c.controls.source.meshDenominator a response
      (if response then x.mu else x.lambda) hm≤GeneralPaperEpochSourcePhaseStorage.window model W k Qv a c hc weights Bc Br epoch := by
  cases response
  · exact ((Nat.le_max_left ..).trans (Nat.le_max_left ..)).trans (cache_children_covered model W k Qv a c hc weights Bc Br epoch)
  · exact ((Nat.le_max_right ..).trans (Nat.le_max_left ..)).trans (cache_children_covered model W k Qv a c hc weights Bc Br epoch)

theorem local_loop_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    GeneralPaperLocalSourceLifetimeStorage.window model W k Qv a c weights Bc Br epoch (GeneralPaperTrajectoryParameters.prepare a.lambda k).period≤
      GeneralPaperEpochSourcePhaseStorage.window model W k Qv a c hc weights Bc Br epoch := by
  have h := Nat.le_max_right (GeneralPaperEpochSourcePhaseStorage.cacheChildren model W k Qv a c hc weights Bc Br epoch)
    (GeneralPaperLocalSourceLifetimeStorage.window model W k Qv a c weights Bc Br epoch (GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  dsimp only [GeneralPaperEpochSourcePhaseStorage.window]
  omega

end Blotto.GeneralPaperEpochPhaseCursorCoverage
