import Blotto.GeneralPaperForestUpdatePrice

/-! Retained actual epochs derive every full-forest update premise. Tree and
state expressions identify already-produced objects, not repeated source or
local-round executions. Both models return the actual next native forest.
-/
namespace Blotto.GeneralPaperActualForestUpdate
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperIntervalLevels
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem final_cap {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epoch : ℕ) (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    ∀ learner j i,i<2^(treeHeight learner a.lambda) → levelAt (node learner trees j) i+
      GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound a.lambda k := by
  dsimp only
  intro learner j i hi
  have hb := GeneralPaperCatalogueOuterValidity.boundary_cap a k Qv weights Bc Br (epoch+1) he learner j i hi
  rw [trees_step,epoch_trees,GeneralPaperCatalogueForestUpdate.updated_level a k Qv weights Bc Br _ _ learner j i hi] at hb
  exact hb

theorem epoch_data {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    (GeneralPaperForestUpdateExecution.run bits index price W c shared trees state).1=(GeneralPaperCatalogueOuterLoop.epoch shared a k trees).1 := by
  dsimp only
  rw [epoch_trees]
  exact GeneralPaperForestUpdateExecution.data bits index price W Qv c hc _ (by rw [hc]; rfl) _ _
    (fun learner => span_power learner a k Qv weights Bc Br)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch (by omega))
    (final_cap a k Qv weights Bc Br epoch he)

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    (GeneralPaperForestUpdateExecution.run true (fun w => w) model.rat W c shared trees state).2≤
      GeneralPaperForestUpdatePrice.profile model.rat W m a.lambda k Qv ∧
    (GeneralPaperForestUpdateExecution.run false (fun _ => 1) model.rat 1 c shared trees state).2≤
      GeneralPaperForestUpdatePrice.arithmeticProfile m a.lambda k Qv := by
  have hv := GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch (by omega : epoch≤_)
  have hf := final_cap a k Qv weights Bc Br epoch he
  exact ⟨GeneralPaperForestUpdatePrice.bit_work model.rat model.monotone W Qv c hc _ _ _
      (fun learner => span_power learner a k Qv weights Bc Br) hv hf,
    GeneralPaperForestUpdatePrice.arithmetic_work model.rat Qv c hc _ _ _
      (fun learner => span_power learner a k Qv weights Bc Br) hv hf⟩

theorem epoch_same_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    (GeneralPaperForestUpdateExecution.run true (fun w => w) model.rat W c shared trees state).1=
      (GeneralPaperForestUpdateExecution.run false (fun _ => 1) model.rat 1 c shared trees state).1 := by
  dsimp only
  rw [epoch_data true (fun w => w) model.rat W k Qv a c hc weights Bc Br epoch he,
    epoch_data false (fun _ => 1) model.rat 1 k Qv a c hc weights Bc Br epoch he]

theorem epoch_valid {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    Valid a k (GeneralPaperForestUpdateExecution.run bits index price W c shared trees state).1 := by
  dsimp only
  rw [epoch_data bits index price W k Qv a c hc weights Bc Br epoch he,←trees_step]
  exact GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br (epoch+1) he

theorem epoch_paths {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    Paths a k (GeneralPaperForestUpdateExecution.run bits index price W c shared trees state).1 := by
  dsimp only
  rw [epoch_data bits index price W k Qv a c hc weights Bc Br epoch he,←trees_step]
  exact GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br (epoch+1) he

theorem prepared_epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := treesAt shared a k epoch
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    (GeneralPaperForestUpdateExecution.run true (fun w => w) model.rat W ready.2.source shared trees state).2≤
      GeneralPaperForestUpdatePrice.profile model.rat W m a.lambda k Qv ∧
    (GeneralPaperForestUpdateExecution.run false (fun _ => 1) model.rat 1 ready.2.source shared trees state).2≤
      GeneralPaperForestUpdatePrice.arithmeticProfile m a.lambda k Qv := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_work model W k Qv (GeneralPaperProxyParameters.alphabet m k) _ rfl weights Bc Br epoch he

end Blotto.GeneralPaperActualForestUpdate
