import Blotto.GeneralPaperOuterEpochExecution

/-! Complete outer epoch prices reuse the returned cache and final local
state. Both cache transports are proofs; no second preparation executes. -/
namespace Blotto.GeneralPaperOuterEpochPrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def localProfile (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet) (Bc Br : ℚ) : ℕ :=
  let p := GeneralPaperProfitParameters.prepare m a.lambda k Qv
  GeneralPaperLocalEpochPrice.profile model W m a.lambda k Qv p.grid.size p.parameters.height p.parameters.leafCount
    (rationalWordWidth Bc) (rationalWordWidth Br) (GeneralPaperTrajectoryParameters.prepare a.lambda k).period

def localArithmeticProfile (m k Qv : ℕ) (a : Alphabet) : ℕ :=
  let p := GeneralPaperProfitParameters.prepare m a.lambda k Qv
  GeneralPaperLocalEpochPrice.arithmeticProfile m a.lambda k Qv p.grid.size p.grid.depth p.parameters.height p.parameters.leafCount
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).period

def profile (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet) (Bc Br : ℚ) : ℕ :=
  GeneralPaperTreeEpochPreparation.profile model W m k Qv a+
    (localProfile model W m k Qv a Bc Br+GeneralPaperForestUpdatePrice.profile model.rat W m a.lambda k Qv+256*W)+128*W

def arithmeticProfile (m k Qv : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperTreeEpochPreparation.arithmeticProfile m k Qv a+
    (localArithmeticProfile m k Qv a+GeneralPaperForestUpdatePrice.arithmeticProfile m a.lambda k Qv+256)+128

theorem finish_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (cache : Cache m k) (ha : cache.alphabet=a)
    (hCache : cache=GeneralPaperCatalogueShared.cache (prepare a k Qv weights Bc Br) a k
      (treesAt (prepare a k Qv weights Bc Br) a k epoch)) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    (GeneralPaperOuterEpochExecution.finish true (fun x => x) model.rat W a c cache ha shared trees).2≤
      localProfile model W m k Qv a Bc Br+GeneralPaperForestUpdatePrice.profile model.rat W m a.lambda k Qv+256*W ∧
    (GeneralPaperOuterEpochExecution.finish false (fun _ => 1) model.rat 1 a c cache ha shared trees).2≤
      localArithmeticProfile m k Qv a+GeneralPaperForestUpdatePrice.arithmeticProfile m a.lambda k Qv+256 := by
  subst cache
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k epoch
  let native := GeneralPaperCatalogueShared.cache shared a k trees
  have hl := GeneralPaperActualLocalEpochPrice.epoch_work model W k Qv a c hc weights Bc Br hWeights epoch
  have hf := GeneralPaperActualForestUpdate.epoch_work model W k Qv a c hc weights Bc Br epoch he
  have hdb := GeneralPaperSelectedLocalEpochExecution.data true (fun x => x) model.rat W Qv native c hc weights Bc Br shared.trajectory.period shared.trajectory.period
  have hdu := GeneralPaperSelectedLocalEpochExecution.data false (fun _ => 1) model.rat 1 Qv native c hc weights Bc Br shared.trajectory.period shared.trajectory.period
  have hb : (GeneralPaperForestUpdateExecution.run true (fun x => x) model.rat W c shared trees
      (GeneralPaperLocalEpochExecution.execute true (fun x => x) model.rat W c native shared.profit shared.trajectory.rows weights Bc Br shared.trajectory.period shared.trajectory.period).1.1).2≤
      GeneralPaperForestUpdatePrice.profile model.rat W m a.lambda k Qv := by
    erw [hdb]
    exact hf.1
  have hu : (GeneralPaperForestUpdateExecution.run false (fun _ => 1) model.rat 1 c shared trees
      (GeneralPaperLocalEpochExecution.execute false (fun _ => 1) model.rat 1 c native shared.profit shared.trajectory.rows weights Bc Br shared.trajectory.period shared.trajectory.period).1.1).2≤
      GeneralPaperForestUpdatePrice.arithmeticProfile m a.lambda k Qv := by
    erw [hdu]
    exact hf.2
  exact ⟨Nat.add_le_add_right (Nat.add_le_add hl.1 hb) _,Nat.add_le_add_right (Nat.add_le_add hl.2 hu) _⟩

theorem work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    (GeneralPaperOuterEpochExecution.run true (fun x => x) model W k Qv a c hc shared trees).2≤profile model W m k Qv a Bc Br ∧
    (GeneralPaperOuterEpochExecution.run false (fun _ => 1) model 1 k Qv a c hc shared trees).2≤arithmeticProfile m k Qv a := by
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k epoch
  have hCache (bits : Bool) (index : ℕ → ℕ) (word : ℕ) :
      (GeneralPaperTreeEpochPreparation.run bits index model word m k Qv a c hc shared.wordWidth trees).1=
        GeneralPaperCatalogueShared.cache shared a k trees := by
    have h := GeneralPaperTreeEpochPreparation.epoch_data bits index model word k Qv a c hc weights Bc Br epoch (by omega : epoch≤_)
    have hp : c.powers=shared.powers := by rw [hc]; rfl
    rw [hp] at h
    exact h
  have hb := (finish_work model W k Qv a c hc weights Bc Br hWeights epoch he _ rfl (hCache true (fun x => x) W)).1
  have hu := (finish_work model W k Qv a c hc weights Bc Br hWeights epoch he _ rfl (hCache false (fun _ => 1) 1)).2
  have hp := GeneralPaperTreeEpochPreparation.epoch_work model W k Qv a c hc weights Bc Br epoch (by omega : epoch≤_)
  exact ⟨Nat.add_le_add_right (Nat.add_le_add hp.1 hb) _,Nat.add_le_add_right (Nat.add_le_add hp.2 hu) _⟩

end Blotto.GeneralPaperOuterEpochPrice
