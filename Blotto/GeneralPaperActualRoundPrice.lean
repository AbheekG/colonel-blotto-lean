import Blotto.GeneralPaperRoundPrice

/-! Actual outer epochs and returned prepared source caches supply every
round premise. Pre-update row recording is the literal native result. -/
namespace Blotto.GeneralPaperActualRoundPrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let cache := GeneralPaperCatalogueShared.cache shared a k trees
    let current := epochRun shared a k trees
    (GeneralPaperRoundExecution.run true (fun x => x) model.rat W c cache current.profit current.T weights Bc Br (stateAt current time)).2≤
      GeneralPaperRoundPrice.profile model W m a.lambda k Qv current.profit.grid.size current.profit.parameters.height current.profit.parameters.leafCount (rationalWordWidth Bc) (rationalWordWidth Br) ∧
    (GeneralPaperRoundExecution.run false (fun _ => 1) model.rat 1 c cache current.profit current.T weights Bc Br (stateAt current time)).2≤
      GeneralPaperRoundPrice.arithmeticProfile m a.lambda k Qv current.profit.grid.size current.profit.grid.depth current.profit.parameters.height current.profit.parameters.leafCount := by
  dsimp only
  rw [epochRun_selected]
  exact GeneralPaperRoundPrice.work model W Qv _ c hc
    (GeneralPaperCatalogueOuterValidity.cache_codes a k Qv weights Bc Br epoch) weights Bc Br hWeights time ht

theorem prepared_epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := treesAt shared a k epoch
    let cache := GeneralPaperCatalogueShared.cache shared a k trees
    let current := epochRun shared a k trees
    (GeneralPaperRoundExecution.run true (fun x => x) model.rat W ready.2.source cache current.profit current.T weights Bc Br (stateAt current time)).2≤
      GeneralPaperRoundPrice.profile model W m a.lambda k Qv current.profit.grid.size current.profit.parameters.height current.profit.parameters.leafCount (rationalWordWidth Bc) (rationalWordWidth Br) ∧
    (GeneralPaperRoundExecution.run false (fun _ => 1) model.rat 1 ready.2.source cache current.profit current.T weights Bc Br (stateAt current time)).2≤
      GeneralPaperRoundPrice.arithmeticProfile m a.lambda k Qv current.profit.grid.size current.profit.grid.depth current.profit.parameters.height current.profit.parameters.leafCount := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_work model W k Qv (GeneralPaperProxyParameters.alphabet m k) _ rfl weights Bc Br hWeights epoch time ht

theorem preupdate_candidate {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperRoundExecution.run bits index price W c cache current.profit current.T weights Bc Br (stateAt current time)).1.candidate.read j=
      ((rowsAt current time).fieldChoice (stateAt current time) j).candidateBid := by
  dsimp only
  rw [GeneralPaperRoundPrice.data bits index price W Qv cache c hc]
  exact GeneralPaperCatalogueEpoch.round_candidate _ _ _ _ _ _ _ _ j

end Blotto.GeneralPaperActualRoundPrice
