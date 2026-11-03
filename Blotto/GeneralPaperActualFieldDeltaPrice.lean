import Blotto.GeneralPaperFieldDeltaPrice

/-! Actual retained epoch caches and reached states derive every code,
prefix and array-length premise. All eight priced arrays equal the native
delta at that local round; source/cache observers introduce no replay.
-/
namespace Blotto.GeneralPaperActualFieldDeltaPrice
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
open GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem field_counts {m k : ℕ} {cache : Cache m k} (current : Run cache) (time : ℕ) (j : Fin m) :
    let plan := (fieldAt current time j).plan
    plan.pCells.partition.count≤GeneralPaperBatchCounterPrice.limit k ∧
    plan.qCells.partition.count≤GeneralPaperBatchCounterPrice.limit k ∧
    plan.lambdaCells.partition.count≤GeneralPaperBatchCounterPrice.limit k ∧
    plan.muCells.partition.count≤GeneralPaperBatchCounterPrice.limit k := by
  dsimp only
  rw [field_plan]
  exact ⟨GeneralPaperActualEpochInstructions.cell_count .p cache j,
    GeneralPaperActualEpochInstructions.cell_count .q cache j,
    GeneralPaperActualEpochInstructions.cell_count .lambda cache j,
    GeneralPaperActualEpochInstructions.cell_count .mu cache j⟩

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperFieldDeltaExecution.run bits index price W c.controls.source.meshDenominator
      (fieldAt current time j) (snapshotAt current time j) (choiceAt current time j)).1=deltaAt current time j := by
  dsimp only
  rw [GeneralPaperFieldDeltaExecution.data bits index price W _ _ _ _ (by rw [hc]; rfl)]
  rfl

theorem work {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (hCodes : GeneralPaperCatalogueEpochMetadata.CodesValid cache)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    let field := fieldAt current time j
    let before := snapshotAt current time j
    let choice := choiceAt current time j
    let mesh := c.controls.source.meshDenominator
    (GeneralPaperFieldDeltaExecution.run true (fun w => w) model.rat W mesh field before choice).2≤
      GeneralPaperFieldDeltaPrice.uniformProfile model.rat W m cache.alphabet.lambda k Qv (GeneralPaperBatchCounterPrice.limit k) ∧
    (GeneralPaperFieldDeltaExecution.run false (fun _ => 1) (fun _ => 1) 1 mesh field before choice).2≤
      GeneralPaperFieldDeltaPrice.uniformArithmeticProfile k (GeneralPaperBatchCounterPrice.limit k) := by
  let current := selected cache Qv weights Bc Br
  have hm : c.controls.source.meshDenominator=(GeneralPaperSourceParameters.prepare k).meshDenominator := by rw [hc]; rfl
  have hg := fun learner => GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j learner
  have hs : GeneralPaperDeltaPlanBounds.PlanSafe cache.alphabet.lambda (fieldAt current time j).plan := by
    rw [field_plan]
    exact GeneralPaperDeltaPlanBounds.actual_plan cache hCodes j
  have hb := GeneralPaperFieldDeltaPrice.bit_work model.rat model.monotone W m cache.alphabet.lambda Qv _
    (fieldAt current time j) (snapshotAt current time j) (choiceAt current time j) hm hg hs
  have hu := GeneralPaperFieldDeltaPrice.arithmetic_work c.controls.source.meshDenominator (fieldAt current time j)
    (snapshotAt current time j) (choiceAt current time j)
  have hn := field_counts current time j
  have hS : (GeneralPaperSourceParameters.prepare k).summarySize≤GeneralPaperBatchCounterPrice.limit k := by
    unfold GeneralPaperBatchCounterPrice.limit; omega
  exact ⟨hb.trans (GeneralPaperFieldDeltaPrice.profile_bound model.rat W m cache.alphabet.lambda Qv _ _ hS hn.1 hn.2.1 hn.2.2.1 hn.2.2.2),
    hu.trans (GeneralPaperFieldDeltaPrice.arithmetic_profile_bound _ _ hS hn.1 hn.2.1 hn.2.2.1 hn.2.2.2)⟩

theorem returned_bound {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperFieldDeltaExecution.run bits index price W c.controls.source.meshDenominator
      (fieldAt current time j) (snapshotAt current time j) (choiceAt current time j)).1.Bounded
        (8*(GeneralPaperSourceParameters.prepare k).meshDenominator) := by
  dsimp only
  rw [data bits index price W Qv cache c hc]
  exact GeneralPaperEpochDeltas.generated_bound _ _ _ (GeneralPaperCatalogueEpochRun.selected_positive cache Qv weights Bc Br time ht j)
    (snapshot_coherent (selected cache Qv weights Bc Br) time j)

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) (j : Fin m) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let current := epochRun shared a k trees
    let field := fieldAt current time j
    let before := snapshotAt current time j
    let choice := choiceAt current time j
    let mesh := c.controls.source.meshDenominator
    (GeneralPaperFieldDeltaExecution.run true (fun w => w) model.rat W mesh field before choice).2≤
      GeneralPaperFieldDeltaPrice.uniformProfile model.rat W m a.lambda k Qv (GeneralPaperBatchCounterPrice.limit k) ∧
    (GeneralPaperFieldDeltaExecution.run false (fun _ => 1) (fun _ => 1) 1 mesh field before choice).2≤
      GeneralPaperFieldDeltaPrice.uniformArithmeticProfile k (GeneralPaperBatchCounterPrice.limit k) := by
  dsimp only
  rw [epochRun_selected]
  exact work model W Qv _ c hc (GeneralPaperCatalogueOuterValidity.cache_codes a k Qv weights Bc Br epoch) weights Bc Br time ht j

theorem prepared_epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) (j : Fin m) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := treesAt shared a k epoch
    let current := epochRun shared a k trees
    let mesh := ready.2.source.controls.source.meshDenominator
    (GeneralPaperFieldDeltaExecution.run true (fun w => w) model.rat W mesh
      (fieldAt current time j) (snapshotAt current time j) (choiceAt current time j)).2≤
      GeneralPaperFieldDeltaPrice.uniformProfile model.rat W m a.lambda k Qv (GeneralPaperBatchCounterPrice.limit k) ∧
    (GeneralPaperFieldDeltaExecution.run false (fun _ => 1) (fun _ => 1) 1 mesh
      (fieldAt current time j) (snapshotAt current time j) (choiceAt current time j)).2≤
      GeneralPaperFieldDeltaPrice.uniformArithmeticProfile k (GeneralPaperBatchCounterPrice.limit k) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_work model W k Qv (GeneralPaperProxyParameters.alphabet m k) _ rfl weights Bc Br epoch time ht j

end Blotto.GeneralPaperActualFieldDeltaPrice
