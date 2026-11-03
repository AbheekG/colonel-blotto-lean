import Blotto.GeneralPaperSourceLifetimeStorage

/-! Whole native source lifetime bounds coexist with the actual retained
classifier/materialized-cache/shared front and literal input scales. A first
completed full trajectory can remain live throughout a second source run.
No global reference word, original-input height or backend bound is assumed. -/
namespace Blotto.GeneralPaperPreparedSourceLifetimeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem prepared_with_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let c := ready.2.source
    let hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
      dsimp only [c,a,ready]
      rw [GeneralPaperPreparedSharedSource.data]
      rfl
    (GeneralPaperClassifierResultStorage.frontFootprint W ready.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W ready.2+GeneralPaperEncodedSharedSource.footprint W ready.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br 0 0)+64*W)+
      GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count≤
        GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
          GeneralPaperSourceLifetimeStorage.profile model W k Qv a weights Bc Br := by
  let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
  let a := ready.1.1.1.2
  let c := ready.2.source
  have ha : a=GeneralPaperProxyParameters.alphabet m k := by
    dsimp only [a,ready]
    rw [GeneralPaperPreparedSharedSource.data]
  have hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
    dsimp only [c,a,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  have he' : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs := by rw [ha]; exact he
  have hbase := GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br 0 0 (Nat.zero_le _) (Nat.zero_le _)
  dsimp only
  exact Nat.add_le_add hbase (GeneralPaperSourceLifetimeStorage.bounded model W k Qv a c hc weights Bc Br hw count he')

theorem with_literal_inputs {m : ℕ} (model : RationalCostModel) (W k Qv B Hc Hr : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv)
    (hB : RationalHeight b B) (hBc : RationalHeight Bc Hc) (hBr : RationalHeight Br Hr) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let c := ready.2.source
    let hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
      dsimp only [c,a,ready]
      rw [GeneralPaperPreparedSharedSource.data]
      rfl
    GeneralPaperPrecallResidentStorage.inputs W m k Qv b Bc Br+
      ((GeneralPaperClassifierResultStorage.frontFootprint W ready.1.1+
        (GeneralPaperMaterializedCacheStorage.gridFootprint W ready.2+GeneralPaperEncodedSharedSource.footprint W ready.1.2+
          GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br 0 0)+64*W)+
        GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count)≤
      GeneralPaperPrecallResidentStorage.inputProfile W m k Qv B Hc Hr+
        (GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
          GeneralPaperSourceLifetimeStorage.profile model W k Qv a weights Bc Br) :=
  Nat.add_le_add (GeneralPaperPrecallResidentStorage.input_scales W m k Qv B Hc Hr b Bc Br hB hBc hBr)
    (prepared_with_residents model W k Qv b hb weights Bc Br hw count he)

theorem retained_first_trajectory {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (execute first a k first.trajectory.epochs).2+
      GeneralPaperSourceLifetimeStorage.window model W k Qv a c hc weights Bc Br count≤
        GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+
          GeneralPaperSourceLifetimeStorage.profile model W k Qv a weights Bc Br :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (GeneralPaperSourceLifetimeStorage.bounded model W k Qv a c hc weights Bc Br hw count he)

end Blotto.GeneralPaperPreparedSourceLifetimeStorage
