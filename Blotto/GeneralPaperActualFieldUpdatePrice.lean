import Blotto.GeneralPaperRoundFieldsExecution

/-! Reached native states derive every per-field composition premise.
The native snapshot/choice observers name already produced objects; no
snapshot, selector or delta execution is replayed by the price theorem.
-/
namespace Blotto.GeneralPaperActualFieldUpdatePrice
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

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
    (GeneralPaperFieldUpdateExecution.run true (fun w => w) model.rat W mesh field before choice).2≤
      GeneralPaperFieldUpdateExecution.profile model.rat W m cache.alphabet.lambda k Qv (GeneralPaperBatchCounterPrice.limit k) ∧
    (GeneralPaperFieldUpdateExecution.run false (fun _ => 1) model.rat 1 mesh field before choice).2≤
      GeneralPaperFieldUpdateExecution.arithmeticProfile k (GeneralPaperBatchCounterPrice.limit k) := by
  let current := selected cache Qv weights Bc Br
  have hm : c.controls.source.meshDenominator=(GeneralPaperSourceParameters.prepare k).meshDenominator := by rw [hc]; rfl
  have hg := fun learner => GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j learner
  have hs : GeneralPaperDeltaPlanBounds.PlanSafe cache.alphabet.lambda (fieldAt current time j).plan := by
    rw [field_plan]
    exact GeneralPaperDeltaPlanBounds.actual_plan cache hCodes j
  have hState := selected_cap cache Qv weights Bc Br time ht j
  have hPositive := GeneralPaperCatalogueEpochRun.selected_positive cache Qv weights Bc Br time ht j
  have hCoherent := snapshot_coherent current time j
  have hn := GeneralPaperActualFieldDeltaPrice.field_counts current time j
  have hS : (GeneralPaperSourceParameters.prepare k).summarySize≤GeneralPaperBatchCounterPrice.limit k := by
    unfold GeneralPaperBatchCounterPrice.limit; omega
  exact ⟨GeneralPaperFieldUpdateExecution.bit_work model.rat model.monotone W m cache.alphabet.lambda Qv _ _
      (fieldAt current time j) (snapshotAt current time j) (choiceAt current time j)
      hm hg hs hState hPositive hCoherent hS hn.1 hn.2.1 hn.2.2.1 hn.2.2.2,
    GeneralPaperFieldUpdateExecution.arithmetic_work model.rat _ _ _ _ _ hS hn.1 hn.2.1 hn.2.2.1 hn.2.2.2⟩

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperFieldUpdateExecution.run bits index price W c.controls.source.meshDenominator
      (fieldAt current time j) (snapshotAt current time j) (choiceAt current time j)).1=fieldAt current (time+1) j := by
  dsimp only
  rw [GeneralPaperFieldUpdateExecution.data bits index price W _ _ _ _ (by rw [hc]; rfl)]
  exact (field_step (selected cache Qv weights Bc Br) time j).symm

theorem returned_cap {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    GeneralPaperEpochFieldState.Bounded (GeneralPaperFieldUpdateExecution.run bits index price W c.controls.source.meshDenominator
      (fieldAt current time j) (snapshotAt current time j) (choiceAt current time j)).1
        (GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) := by
  dsimp only
  rw [data bits index price W Qv cache c hc]
  exact selected_cap cache Qv weights Bc Br (time+1) ht j

end Blotto.GeneralPaperActualFieldUpdatePrice
