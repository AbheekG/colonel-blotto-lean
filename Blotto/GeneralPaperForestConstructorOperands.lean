import Blotto.GeneralPaperSourceControllerContextStorage

/-! Actual reached final fields derive every complete forest-constructor
callback node cap. Native updated nodes share the existing per-field source
node envelope; the bound is never multiplied by the number of instructions. -/
namespace Blotto.GeneralPaperForestConstructorOperands
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalCache
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def nodeProfile (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperRetainedForestNodes.perField lambda k (GeneralPaperTrajectoryParameters.prepare lambda k).epochs*
    GeneralPaperSparseNodeBits.perNode W m lambda k Qv

theorem element_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (j : Fin m) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    (GeneralPaperForestUpdateExecution.element true (fun w => w) model.rat W c shared trees state learner j).1=
      (GeneralPaperIntervalBatch.run c.powers (treeHeight learner a.lambda) (span learner shared) (node learner trees j)
        (GeneralPaperCatalogueCellHistory.batchOfState learner state j)).node := by
  dsimp only [GeneralPaperForestUpdateExecution.element]
  exact congrArg (fun r => r.node) (GeneralPaperEpochNodeUpdate.data true (fun w => w) model.rat W Qv c hc learner _ j _ _ _
    (span_power learner a k Qv weights Bc Br)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch (by omega) learner j)
    (GeneralPaperActualForestUpdate.final_cap a k Qv weights Bc Br epoch he learner j))

theorem element_bound {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (j : Fin m) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    GeneralPaperSparseNodeBits.footprint W (GeneralPaperForestUpdateExecution.element true (fun w => w) model.rat W c shared trees state learner j).1≤
      nodeProfile W m a.lambda k Qv := by
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k epoch
  let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
  let entries := GeneralPaperCatalogueCellHistory.batchOfState learner state j
  have hb := GeneralPaperEncodedForestStorage.partial_batch W k Qv a weights Bc Br epoch entries.length he learner j
  change GeneralPaperSparseNodeBits.footprint W (GeneralPaperIntervalBatch.run shared.powers (treeHeight learner a.lambda)
    (span learner shared) (node learner trees j) (entries.take entries.length)).node≤_ at hb
  simp only [List.take_length] at hb
  have hd := element_data model W k Qv a c hc weights Bc Br epoch he learner j
  dsimp only at hd ⊢
  rw [hd]
  have hp : c.powers=shared.powers := by rw [hc]; rfl
  rw [hp]
  exact hb

theorem returned {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    GeneralPaperEncodedForestStorage.footprint W (GeneralPaperForestUpdateExecution.run true (fun w => w) model.rat W c shared trees state).1≤
      GeneralPaperEncodedForestStorage.profile W m a.lambda k Qv := by
  dsimp only
  rw [GeneralPaperActualForestUpdate.epoch_data true (fun w => w) model.rat W k Qv a c hc weights Bc Br epoch he,←trees_step]
  exact GeneralPaperEncodedForestStorage.actual W k Qv a weights Bc Br (epoch+1) he

end Blotto.GeneralPaperForestConstructorOperands
