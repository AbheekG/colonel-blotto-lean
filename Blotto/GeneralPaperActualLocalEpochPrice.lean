import Blotto.GeneralPaperLocalEpochPrice

/-! Actual forests and returned source preparation supply every local epoch
premise, including code validity and the retained period capacity. -/
namespace Blotto.GeneralPaperActualLocalEpochPrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch : ℕ) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let cache := GeneralPaperCatalogueShared.cache shared a k trees
    (GeneralPaperLocalEpochExecution.execute true (fun x => x) model.rat W c cache shared.profit shared.trajectory.rows weights Bc Br shared.trajectory.period shared.trajectory.period).2≤
      GeneralPaperLocalEpochPrice.profile model W m a.lambda k Qv shared.profit.grid.size shared.profit.parameters.height shared.profit.parameters.leafCount
        (rationalWordWidth Bc) (rationalWordWidth Br) shared.trajectory.period ∧
    (GeneralPaperLocalEpochExecution.execute false (fun _ => 1) model.rat 1 c cache shared.profit shared.trajectory.rows weights Bc Br shared.trajectory.period shared.trajectory.period).2≤
      GeneralPaperLocalEpochPrice.arithmeticProfile m a.lambda k Qv shared.profit.grid.size shared.profit.grid.depth shared.profit.parameters.height shared.profit.parameters.leafCount shared.trajectory.period := by
  exact GeneralPaperLocalEpochPrice.work model W Qv _ c hc
    (GeneralPaperCatalogueOuterValidity.cache_codes a k Qv weights Bc Br epoch) weights Bc Br hWeights _ (Nat.le_refl _)

theorem prepared_epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch : ℕ) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := treesAt shared a k epoch
    let cache := GeneralPaperCatalogueShared.cache shared a k trees
    (GeneralPaperLocalEpochExecution.execute true (fun x => x) model.rat W ready.2.source cache shared.profit shared.trajectory.rows weights Bc Br shared.trajectory.period shared.trajectory.period).2≤
      GeneralPaperLocalEpochPrice.profile model W m a.lambda k Qv shared.profit.grid.size shared.profit.parameters.height shared.profit.parameters.leafCount
        (rationalWordWidth Bc) (rationalWordWidth Br) shared.trajectory.period ∧
    (GeneralPaperLocalEpochExecution.execute false (fun _ => 1) model.rat 1 ready.2.source cache shared.profit shared.trajectory.rows weights Bc Br shared.trajectory.period shared.trajectory.period).2≤
      GeneralPaperLocalEpochPrice.arithmeticProfile m a.lambda k Qv shared.profit.grid.size shared.profit.grid.depth shared.profit.parameters.height shared.profit.parameters.leafCount shared.trajectory.period := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_work model W k Qv (GeneralPaperProxyParameters.alphabet m k) _ rfl weights Bc Br hWeights epoch

end Blotto.GeneralPaperActualLocalEpochPrice
