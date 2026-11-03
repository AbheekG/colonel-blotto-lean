import Blotto.GeneralPaperTreeEpochConstructionStorage

/-! Complete native forest-update and tree-to-epoch parents coexist with
actual retained source residents and the full source/controller/selector
context. Prepared data derives all native caches and capacities; no new
source, epoch, selector or parameter pass is executed by these observers. -/
namespace Blotto.GeneralPaperActualEpochParentStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueTreeCache GeneralPaperCatalogueOccurrenceHistory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count innerCount rowCount tailCount remaining : ℕ)
    (hcount : count≤m) (hi : innerCount≤c.controls.source.summarySize)
    (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) (r : Fin c.controls.source.summarySize) (learner : Learner) : ℕ :=
  let shared := prepare a k Qv weights Bc Br
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  GeneralPaperForestFamilyConstructionStorage.window model W k Qv a c weights Bc Br epoch count remaining hcount+
    GeneralPaperTreeEpochConstructionStorage.window model W m k Qv a c hc (GeneralPaperQuantileComparison.width a.lambda k) trees
      count innerCount rowCount tailCount hcount hi hr ht j i q r learner

def profile (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperForestFamilyConstructionStorage.profile model W m k Qv a+GeneralPaperTreeEpochConstructionStorage.profile model W m k Qv a

theorem actual {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count innerCount rowCount tailCount remaining : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (hcount : count≤m) (hi : innerCount≤c.controls.source.summarySize)
    (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) (r : Fin c.controls.source.summarySize) (learner : Learner) :
    window model W k Qv a c hc weights Bc Br epoch count innerCount rowCount tailCount remaining hcount hi hr ht j i q r learner≤profile model W m k Qv a :=
  Nat.add_le_add (GeneralPaperForestFamilyConstructionStorage.bounded model W k Qv a c hc weights Bc Br epoch count remaining hcount he)
    (GeneralPaperTreeEpochConstructionStorage.bounded model W m k Qv a c hc (GeneralPaperQuantileComparison.width a.lambda k) rfl _
      (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch (by omega))
      (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch (by omega))
      count innerCount rowCount tailCount hcount hi hr ht j i q r learner)

theorem prepared_with_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count innerCount rowCount tailCount remaining : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (hcount : count≤m) (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) (learner : Learner) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let c := ready.2.source
    let hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
      dsimp only [c,a,ready]
      rw [GeneralPaperPreparedSharedSource.data]
      rfl
    ∀ (r : Fin c.controls.source.summarySize) (hi : innerCount≤c.controls.source.summarySize),
    (GeneralPaperClassifierResultStorage.frontFootprint W ready.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W ready.2+GeneralPaperEncodedSharedSource.footprint W ready.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch (GeneralPaperTrajectoryParameters.prepare a.lambda k).period)+64*W)+
      window model W k Qv a c hc weights Bc Br epoch count innerCount rowCount tailCount remaining hcount hi hr ht j i q r learner≤
        GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+profile model W m k Qv a := by
  let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
  let a := ready.1.1.1.2
  let c := ready.2.source
  have halpha : a=GeneralPaperProxyParameters.alphabet m k := by
    dsimp only [a,ready]
    rw [GeneralPaperPreparedSharedSource.data]
  have hcache : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
    dsimp only [c,a,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  have he' : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs := by rw [halpha]; exact he
  have hbase := GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br epoch
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).period (by omega) (by rw [halpha])
  dsimp only
  intro r hi
  exact Nat.add_le_add hbase (actual model W k Qv a c hcache weights Bc Br
    epoch count innerCount rowCount tailCount remaining he' hcount hi hr ht j i q r learner)

theorem with_source_context {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (htime : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount tailCount : ℕ)
    (hcount : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (innerCount appendCount summaryCount : ℕ)
    (ha : appendCount≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (hs : summaryCount≤c.controls.source.summarySize) (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1))
    (r : Fin c.controls.source.summarySize) (learner : Learner) :
    GeneralPaperSourceControllerContextStorage.window model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time
      j i count copied rowCount hcount hr left right innerCount appendCount ha+
      window model W k Qv a c hc weights Bc Br epoch rowCount summaryCount count tailCount innerCount hr hs hcount ht j i q r learner≤
        GeneralPaperSourceControllerContextStorage.profile model W k Qv a weights Bc Br+profile model W m k Qv a :=
  Nat.add_le_add (GeneralPaperSourceControllerContextStorage.actual model W k Qv a weights Bc Br hWeights epoch time he htime
    j i count copied rowCount hcount hr left right innerCount appendCount ha)
    (actual model W k Qv a c hc weights Bc Br epoch rowCount summaryCount count tailCount innerCount he hr hs hcount ht j i q r learner)

theorem retained_first_trajectory {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (epoch count innerCount rowCount tailCount remaining : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (hcount : count≤m) (hi : innerCount≤c.controls.source.summarySize)
    (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) (r : Fin c.controls.source.summarySize) (learner : Learner) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
      window model W k Qv a c hc weights Bc Br epoch count innerCount rowCount tailCount remaining hcount hi hr ht j i q r learner≤
        GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+profile model W m k Qv a :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (actual model W k Qv a c hc weights Bc Br epoch count innerCount rowCount tailCount remaining he hcount hi hr ht j i q r learner)

end Blotto.GeneralPaperActualEpochParentStorage
