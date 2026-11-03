import Blotto.GeneralPaperPhysicalRowPhaseCoverage

/-! Embed an actual reached response and its physical child cursors into
the checked source's finite maxima. Prefix states, returned forests and
prepared caches are the native ones; all embeddings erase at execution. -/
namespace Blotto.GeneralPaperPhysicalSourcePhaseCoverage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochCache
open GeneralPaperFiniteStorageWindows GeneralPaperPhysicalResponseNativeStorage
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

def localResponse {m k : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br delta : ℚ) (capacity : ℕ) (time : Fin capacity) : FixedArrayTable m ℕ :=
  let first := (GeneralPaperEpochInitialFamilyPrice.run true (fun w => w) model.rat W cache).1
  let previous := GeneralPaperPhysicalResponseEpoch.run true (fun w => w) model.rat model W c cache profit T
    weights Bc Br delta first capacity time.val
  (GeneralPaperRoundExecution.run true (fun w => w) model.rat W c cache profit T weights Bc Br previous.1.1.1).1.response

theorem local_point {m k : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br delta : ℚ) (capacity : ℕ) (time : Fin capacity) :
    GeneralPaperPhysicalResponseStorage.window model W cache.alphabet delta
      (localResponse model W c cache profit T weights Bc Br delta capacity time) Br≤
      epochChildren model W c cache profit T weights Bc Br delta capacity := by
  let first := (GeneralPaperEpochInitialFamilyPrice.run true (fun w => w) model.rat W cache).1
  exact observed_le_maximum (fun t : Fin capacity => roundWindow model W c cache profit T weights Bc Br delta
    (GeneralPaperPhysicalResponseEpoch.run true (fun w => w) model.rat model W c cache profit T weights Bc Br delta
      first capacity t.val).1.1.1) time

def outerResponse {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda)
    (time : Fin shared.trajectory.period) : FixedArrayTable m ℕ :=
  let cache := (GeneralPaperTreeEpochPreparation.run true (fun w => w) model W m k Qv a c hc shared.wordWidth trees).1
  localResponse model W c cache shared.profit shared.trajectory.rows shared.weights shared.Bc shared.Br delta shared.trajectory.period time

theorem outer_point {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda)
    (time : Fin shared.trajectory.period) :
    GeneralPaperPhysicalResponseStorage.window model W a delta
      (outerResponse model W k Qv a c hc shared delta trees time) shared.Br≤
      outerChildren model W k Qv a c hc shared delta trees :=
  local_point model W c _ shared.profit shared.trajectory.rows shared.weights shared.Bc shared.Br delta shared.trajectory.period time

def sourceResponse {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (count : ℕ) (epoch : Fin count) (time : Fin shared.trajectory.period) : FixedArrayTable m ℕ :=
  let delta := (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1
  let previous := GeneralPaperPhysicalResponseSourceExecution.run true (fun w => w) model W k Qv a c hc shared delta epoch.val
  outerResponse model W k Qv a c hc shared delta previous.1.1.1 time

theorem source_point {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (count : ℕ) (epoch : Fin count) (time : Fin shared.trajectory.period) :
    GeneralPaperPhysicalResponseStorage.window model W a (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1
      (sourceResponse model W k Qv qbar a c hc shared count epoch time) shared.Br≤
      sourceChildren model W k Qv qbar a c hc shared count := by
  have hp := outer_point model W k Qv a c hc shared
    (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1
    (GeneralPaperPhysicalResponseSourceExecution.run true (fun w => w) model W k Qv a c hc shared
      (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1 epoch.val).1.1.1 time
  have hn := observed_le_maximum (fun e : Fin count => outerChildren model W k Qv a c hc shared
    (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1
    (GeneralPaperPhysicalResponseSourceExecution.run true (fun w => w) model W k Qv a c hc shared
      (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1 e.val).1.1.1) epoch
  exact hp.trans hn

theorem child_in_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    sourceChildren model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count≤
      extraWindow model W k Qv qbar a c hc weights Bc Br count := by
  unfold extraWindow
  exact (Nat.le_add_left ..).trans (Nat.le_add_right ..)

theorem shift_in_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    GeneralPaperPhysicalShiftStorage.window model W m qbar a.C≤extraWindow model W k Qv qbar a c hc weights Bc Br count := by
  unfold extraWindow
  exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)

theorem response_in_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) (epoch : Fin count)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    GeneralPaperPhysicalResponseStorage.window model W a (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1
      (sourceResponse model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count epoch time) Br≤
      extraWindow model W k Qv qbar a c hc weights Bc Br count :=
  (source_point model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count epoch time).trans (child_in_extra model W k Qv qbar a c hc weights Bc Br count)

theorem decoder_in_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) (epoch : Fin count)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).period) (j : Fin m) :
    GeneralPaperPhysicalBidStorage.window model W a (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1
      ((sourceResponse model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count epoch time).read j)≤
      extraWindow model W k Qv qbar a c hc weights Bc Br count :=
  (GeneralPaperPhysicalRowPhaseCoverage.decoder_covered model W a _ _ Br j).trans
    (response_in_extra model W k Qv qbar a c hc weights Bc Br count epoch time)

theorem prefix_in_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) (epoch : Fin count)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).period) (used : ℕ) (hu : used≤m) :
    GeneralPaperPhysicalResponseStorage.rowPrefix model W a (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1
      (sourceResponse model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count epoch time) used hu≤
      extraWindow model W k Qv qbar a c hc weights Bc Br count :=
  (GeneralPaperPhysicalRowPhaseCoverage.prefix_covered model W a _ _ Br used hu).trans
    (response_in_extra model W k Qv qbar a c hc weights Bc Br count epoch time)

theorem budget_in_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) (epoch : Fin count)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let codes := sourceResponse model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count epoch time
    let delta := (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1
    GeneralPaperRowBudgetStorage.window model (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 Br≤
      extraWindow model W k Qv qbar a c hc weights Bc Br count :=
  (GeneralPaperPhysicalRowPhaseCoverage.budget_covered model W a _ _ Br).trans
    (response_in_extra model W k Qv qbar a c hc weights Bc Br count epoch time)

theorem scan_in_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) (epoch : Fin count)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).period) (used : ℕ) (hu : used+1≤m) :
    let codes := sourceResponse model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count epoch time
    let delta := (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1
    GeneralPaperRowBudgetStorage.localWindow model (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 used hu≤
      extraWindow model W k Qv qbar a c hc weights Bc Br count :=
  (GeneralPaperPhysicalRowPhaseCoverage.physical_scan_covered model W a _ _ Br used hu).trans
    (response_in_extra model W k Qv qbar a c hc weights Bc Br count epoch time)

theorem final_in_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) (epoch : Fin count)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let codes := sourceResponse model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count epoch time
    let delta := (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1
    GeneralPaperRowBudgetStorage.finalWindow model (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 Br≤
      extraWindow model W k Qv qbar a c hc weights Bc Br count :=
  (GeneralPaperPhysicalRowPhaseCoverage.final_check_covered model W a _ _ Br).trans
    (response_in_extra model W k Qv qbar a c hc weights Bc Br count epoch time)

theorem empty_local {m k : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br delta : ℚ) : epochChildren model W c cache profit T weights Bc Br delta 0=0 := by
  unfold epochChildren
  dsimp only
  exact maximum_empty _

theorem empty_source {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) : sourceChildren model W k Qv qbar a c hc shared 0=0 := by
  unfold sourceChildren
  dsimp only
  exact maximum_empty _

theorem resident_in_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    rationalWordWidth (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1≤
      extraWindow model W k Qv qbar a c hc weights Bc Br count := by
  unfold extraWindow
  exact ((Nat.le_add_left ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)

theorem flags_in_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    flagWindow W a.lambda k count≤extraWindow model W k Qv qbar a c hc weights Bc Br count :=
  Nat.le_add_left _ _

end Blotto.GeneralPaperPhysicalSourcePhaseCoverage
