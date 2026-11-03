import Blotto.GeneralPaperReadyPhaseCursorCoverage

/-! Native round callbacks, snapshot fills, selector/output fills and
initialization prefixes lie in the corresponding finite phase maxima.
Counter embeddings preserve native values. Copy/delta bounds use actual
prepared leaf and source cell capacities, including final prefixes. -/
namespace Blotto.GeneralPaperRoundPhaseCursorCoverage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperFiniteStorageWindows GeneralPaperStorageCursorPacking
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

theorem copy_cap (m lambda k Qv : ℕ)
    (copied : Fin ((GeneralPaperProfitParameters.prepare m lambda k Qv).parameters.leafCount+1)) :
    copied.val≤GeneralPaperRoundPhaseStorage.progressCap m lambda k Qv :=
  (Nat.le_of_lt_succ copied.isLt).trans (GeneralPaperRoundPhaseStorage.native_caps m lambda k Qv _ (by simp))

theorem inner_cap (m lambda k Qv : ℕ) (inner : Fin (GeneralPaperBatchCounterPrice.limit k+2)) :
    inner.val≤GeneralPaperRoundPhaseStorage.progressCap m lambda k Qv := by
  have h := GeneralPaperRoundPhaseStorage.native_caps m lambda k Qv (GeneralPaperBatchCounterPrice.limit k+1) (by simp)
  have hi := inner.isLt
  omega

theorem callback_point {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size)
    (copied : Fin ((GeneralPaperProfitParameters.prepare m a.lambda k Qv).parameters.leafCount+1))
    (inner : Fin (GeneralPaperBatchCounterPrice.limit k+2)) :
    GeneralPaperSelectedRowConstructionStorage.sourceWindow model W k Qv a (prepare a k Qv weights Bc Br)
      weights Bc Br epoch time j i count copied.val rowCount hc hr left right inner.val≤
        GeneralPaperRoundPhaseStorage.callbacks model W k Qv a weights Bc Br epoch time :=
  observed_le_maximum (GeneralPaperRoundPhaseStorage.callbackWindow model W k Qv a weights Bc Br epoch time)
    (j,i,counter ((GeneralPaperSourceParameters.prepare k).summarySize+2) count hc,counter m rowCount hr,left,right,
      counter (GeneralPaperRoundPhaseStorage.progressCap m a.lambda k Qv) copied.val (copy_cap m a.lambda k Qv copied),
      counter (GeneralPaperRoundPhaseStorage.progressCap m a.lambda k Qv) inner.val (inner_cap m a.lambda k Qv inner))

theorem callback_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size)
    (copied : Fin ((GeneralPaperProfitParameters.prepare m a.lambda k Qv).parameters.leafCount+1))
    (inner : Fin (GeneralPaperBatchCounterPrice.limit k+2)) :
    GeneralPaperSelectedRowConstructionStorage.sourceWindow model W k Qv a (prepare a k Qv weights Bc Br)
      weights Bc Br epoch time j i count copied.val rowCount hc hr left right inner.val≤
        GeneralPaperRoundPhaseStorage.window model W k Qv a c weights Bc Br epoch time := by
  have h := callback_point model W k Qv a weights Bc Br epoch time j i count rowCount hc hr left right copied inner
  dsimp only [GeneralPaperRoundPhaseStorage.window]
  exact h.trans ((Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans (Nat.le_add_right ..)))

theorem snapshot_cap (m lambda k Qv : ℕ) (used : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    used.val≤GeneralPaperRoundPhaseStorage.progressCap m lambda k Qv := by
  have h := GeneralPaperRoundPhaseStorage.native_caps m lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2) (by simp)
  exact used.isLt.le.trans h

theorem snapshot_point {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time count innerCount : ℕ)
    (hc : count≤m) (hi : innerCount≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (used copied : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    let shared := prepare a k Qv weights Bc Br
    let current := epochRun shared a k (GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch)
    GeneralPaperSnapshotFamilyConstructionStorage.window model W c (stateAt current time).fields count innerCount used.val copied.val hc hi≤
      GeneralPaperRoundPhaseStorage.snapshots model W k Qv a c weights Bc Br epoch time :=
  observed_le_maximum (GeneralPaperRoundPhaseStorage.snapshotWindow model W k Qv a c weights Bc Br epoch time)
    (counter m count hc,counter (GeneralPaperSourceParameters.prepare k).summarySize innerCount hi,
      counter (GeneralPaperRoundPhaseStorage.progressCap m a.lambda k Qv) used.val (snapshot_cap m a.lambda k Qv used),
      counter (GeneralPaperRoundPhaseStorage.progressCap m a.lambda k Qv) copied.val (snapshot_cap m a.lambda k Qv copied))

theorem snapshot_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time count innerCount : ℕ)
    (hc : count≤m) (hi : innerCount≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (used copied : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    let shared := prepare a k Qv weights Bc Br
    let current := epochRun shared a k (GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch)
    GeneralPaperSnapshotFamilyConstructionStorage.window model W c (stateAt current time).fields count innerCount used.val copied.val hc hi≤
      GeneralPaperRoundPhaseStorage.window model W k Qv a c weights Bc Br epoch time := by
  have h := snapshot_point model W k Qv a c weights Bc Br epoch time count innerCount hc hi used copied
  exact h.trans ((Nat.le_max_left ..).trans (Nat.le_add_right ..))

theorem selector_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time count : ℕ) (hc : count≤m) :
    GeneralPaperActualDPConstructionStorage.window true (fun w => w) model.rat W W k Qv a (prepare a k Qv weights Bc Br)
      weights Bc Br epoch time count hc≤GeneralPaperRoundPhaseStorage.window model W k Qv a c weights Bc Br epoch time := by
  have h : GeneralPaperActualDPConstructionStorage.window true (fun w => w) model.rat W W k Qv a (prepare a k Qv weights Bc Br)
      weights Bc Br epoch time count hc≤GeneralPaperRoundPhaseStorage.selectors model W k Qv a weights Bc Br epoch time :=
    observed_le_maximum (GeneralPaperRoundPhaseStorage.selectorWindow model W k Qv a weights Bc Br epoch time) (counter m count hc)
  exact h.trans ((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_add_right ..)))

theorem local_initial_covered {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ) (hc : count≤m)
    (inner : Fin (GeneralPaperBatchCounterPrice.limit k+2)) :
    GeneralPaperEpochInitialConstructionStorage.familyWindow model W (GeneralPaperLocalSourceLifetimeStorage.cache a k Qv weights Bc Br epoch)
      count inner.val hc≤GeneralPaperLocalSourceLifetimeStorage.initialPeak model W k Qv a weights Bc Br epoch :=
  observed_le_maximum (GeneralPaperLocalSourceLifetimeStorage.initialWindow model W k Qv a weights Bc Br epoch)
    (counter m count hc,counter (GeneralPaperRoundPhaseStorage.progressCap m a.lambda k Qv) inner.val (inner_cap m a.lambda k Qv inner))

theorem forest_initial_covered (W m lambda count : ℕ) (hc : count≤m) :
    GeneralPaperInitialForestConstructionStorage.window W m lambda count hc≤GeneralPaperSourceLifetimeStorage.initialPeak W m lambda :=
  observed_le_maximum (fun index : Fin (m+1) =>
    GeneralPaperInitialForestConstructionStorage.window W m lambda index.val (Nat.le_of_lt_succ index.isLt)) (counter m count hc)

end Blotto.GeneralPaperRoundPhaseCursorCoverage
