import Blotto.GeneralPaperActualLocalEpochPrice

/-! Prepare the cache once, run one local epoch and update its incoming
forest from the returned final fields. Alphabet transports erase; the
constructed cache and all retained source controls are reused. -/
namespace Blotto.GeneralPaperOuterEpochExecution
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def finish {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (ha : cache.alphabet=a)
    (shared : Shared m) (trees : Trees m a.lambda) : (Trees m a.lambda × Array (FixedArrayTable m ℕ)) × ℕ :=
  let localResult := GeneralPaperLocalEpochExecution.execute bits index price W c cache shared.profit shared.trajectory.rows
    shared.weights shared.Bc shared.Br shared.trajectory.period shared.trajectory.period
  let inputTrees : Trees m cache.alphabet.lambda := ha.symm ▸ trees
  let updated := GeneralPaperForestUpdateExecution.run bits index price W c shared inputTrees localResult.1.1
  ((ha ▸ updated.1,localResult.1.2),localResult.2+updated.2+256*W)

def run {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (trees : Trees m a.lambda) : (Trees m a.lambda × Array (FixedArrayTable m ℕ)) × ℕ :=
  let prepared := GeneralPaperTreeEpochPreparation.run bits index model W m k Qv a c hc shared.wordWidth trees
  let computed := finish bits index model.rat W a c prepared.1 rfl shared trees
  (computed.1,prepared.2+computed.2+128*W)

theorem finish_data {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (cache : Cache m k) (ha : cache.alphabet=a)
    (hCache : cache=GeneralPaperCatalogueShared.cache (prepare a k Qv weights Bc Br) a k
      (treesAt (prepare a k Qv weights Bc Br) a k epoch)) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    (finish bits index price W a c cache ha shared trees).1=GeneralPaperCatalogueOuterLoop.epoch shared a k trees := by
  subst cache
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k epoch
  let native := GeneralPaperCatalogueShared.cache shared a k trees
  have hl := GeneralPaperSelectedLocalEpochExecution.data bits index price W Qv native c hc weights Bc Br shared.trajectory.period shared.trajectory.period
  change (GeneralPaperLocalEpochExecution.execute bits index price W c native shared.profit shared.trajectory.rows
    shared.weights shared.Bc shared.Br shared.trajectory.period shared.trajectory.period).1=
      GeneralPaperCatalogueEpoch.execute native shared.powers shared.profit shared.trajectory.rows shared.weights shared.Bc shared.Br (initial native) shared.trajectory.period at hl
  change ((GeneralPaperForestUpdateExecution.run bits index price W c shared trees
    (GeneralPaperLocalEpochExecution.execute bits index price W c native shared.profit shared.trajectory.rows shared.weights shared.Bc shared.Br shared.trajectory.period shared.trajectory.period).1.1).1,
    (GeneralPaperLocalEpochExecution.execute bits index price W c native shared.profit shared.trajectory.rows shared.weights shared.Bc shared.Br shared.trajectory.period shared.trajectory.period).1.2)=_
  erw [hl]
  erw [GeneralPaperActualForestUpdate.epoch_data bits index price W k Qv a c hc weights Bc Br epoch he]
  rfl

theorem data {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    (run bits index model W k Qv a c hc shared trees).1=GeneralPaperCatalogueOuterLoop.epoch shared a k trees := by
  have hCache : (GeneralPaperTreeEpochPreparation.run bits index model W m k Qv a c hc
      (prepare a k Qv weights Bc Br).wordWidth (treesAt (prepare a k Qv weights Bc Br) a k epoch)).1=
      GeneralPaperCatalogueShared.cache (prepare a k Qv weights Bc Br) a k (treesAt (prepare a k Qv weights Bc Br) a k epoch) := by
    have h := GeneralPaperTreeEpochPreparation.epoch_data bits index model W k Qv a c hc weights Bc Br epoch (by omega : epoch≤_)
    have hp : c.powers=(prepare a k Qv weights Bc Br).powers := by rw [hc]; rfl
    rw [hp] at h
    exact h
  exact finish_data bits index model.rat W k Qv a c hc weights Bc Br epoch he _ rfl hCache

end Blotto.GeneralPaperOuterEpochExecution
