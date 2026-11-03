import Blotto.GeneralPaperActualSourceTrajectoryStorage

/-! Native initialization, recursive controllers and append buffers join
the full actual source/update/selector/root/DP context. Prepared returns
derive their own cache/trajectory parameters; all observed constructors and
data transfers are erased, without executing a second source pass. -/
namespace Blotto.GeneralPaperSourceControllerContextStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem prepared_initial {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count innerCount : ℕ) (hc : count≤m) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueShared.cache r.1.2 a k trees
    GeneralPaperEpochInitialConstructionStorage.familyWindow model W cache count innerCount hc≤
      GeneralPaperEpochInitialConstructionStorage.familyProfile model W m a.lambda k Qv :=
  GeneralPaperEpochInitialConstructionStorage.family_bounded model W Qv _ count innerCount hc

theorem with_initial_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count innerCount : ℕ) (hc : count≤m)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueShared.cache r.1.2 a k trees
    (GeneralPaperClassifierResultStorage.frontFootprint W r.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch 0)+64*W)+
      GeneralPaperEpochInitialConstructionStorage.familyWindow model W cache count innerCount hc≤
        GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
          GeneralPaperEpochInitialConstructionStorage.familyProfile model W m a.lambda k Qv :=
  Nat.add_le_add (GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br epoch 0 he (Nat.zero_le _))
    (prepared_initial model W k Qv b weights Bc Br epoch count innerCount hc)

theorem with_forest_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) (hc : count≤m) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    (GeneralPaperClassifierResultStorage.frontFootprint W r.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br 0 0)+64*W)+
      GeneralPaperInitialForestConstructionStorage.window W m a.lambda count hc≤
        GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
          GeneralPaperInitialForestConstructionStorage.profile W m a.lambda :=
  Nat.add_le_add (GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br 0 0 (Nat.zero_le _) (Nat.zero_le _))
    (GeneralPaperInitialForestConstructionStorage.bounded W m _ count hc)

def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (shared : Shared m) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (innerCount appendCount : ℕ)
    (ha : appendCount≤shared.trajectory.period) : ℕ :=
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let first := (GeneralPaperCatalogueOuterLoop.execute shared a k epoch).2
  let chunk := (GeneralPaperCatalogueOuterLoop.epoch shared a k trees).2
  GeneralPaperSelectedRowConstructionStorage.sourceWindow model W k Qv a shared weights Bc Br epoch time j i count copied rowCount hc hr left right innerCount+
    GeneralPaperInitialForestConstructionStorage.window W m a.lambda rowCount hr+
    GeneralPaperEpochInitialConstructionStorage.familyWindow model W cache rowCount innerCount hr+
    GeneralPaperTrajectoryControllerStorage.localWindow W shared.trajectory.period time+
    GeneralPaperTrajectoryControllerStorage.outerWindow W shared.trajectory.epochs shared.trajectory.rows epoch+
    GeneralPaperTrajectoryAppendStorage.window W shared.trajectory.rows first chunk appendCount (by rw [GeneralPaperCatalogueOuterLoop.epoch_size]; exact ha)

def profile {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  let t := GeneralPaperTrajectoryParameters.prepare a.lambda k
  GeneralPaperSelectedRowConstructionStorage.sourceProfile model W k Qv a weights Bc Br+
    GeneralPaperInitialForestConstructionStorage.profile W m a.lambda+
    GeneralPaperEpochInitialConstructionStorage.familyProfile model W m a.lambda k Qv+
    GeneralPaperTrajectoryControllerStorage.localProfile W t.period+
    GeneralPaperTrajectoryControllerStorage.outerProfile W t.epochs t.rows+
    GeneralPaperTrajectoryAppendStorage.profile W m t.rows t.period (GeneralPaperDecoderControls.operandWidth a.lambda)

theorem actual {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (innerCount appendCount : ℕ)
    (ha : appendCount≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    window model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr left right innerCount appendCount ha≤
      profile model W k Qv a weights Bc Br := by
  have hbase := GeneralPaperSelectedRowConstructionStorage.actual model W k Qv a weights Bc Br hWeights epoch time (by omega) ht
    j i count copied rowCount hc hr left right innerCount
  have hforest := GeneralPaperInitialForestConstructionStorage.bounded W m a.lambda rowCount hr
  have hinitial := GeneralPaperEpochInitialConstructionStorage.family_bounded model W Qv
    (GeneralPaperCatalogueShared.cache (prepare a k Qv weights Bc Br) a k
      (GeneralPaperCatalogueOuterLoop.treesAt (prepare a k Qv weights Bc Br) a k epoch)) rowCount innerCount hr
  have hlocal := GeneralPaperTrajectoryControllerStorage.local_bounded W (GeneralPaperTrajectoryParameters.prepare a.lambda k).period time (by omega)
  have houter := GeneralPaperTrajectoryControllerStorage.outer_bounded W (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows epoch (by omega)
  have happend := GeneralPaperActualSourceTrajectoryStorage.append W k Qv a weights Bc Br epoch appendCount he ha
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hbase hforest) hinitial) hlocal) houter) happend

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) (innerCount appendCount : ℕ) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    ∀ (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (ha : appendCount≤r.1.2.trajectory.period),
    window model W k Qv a r.1.2 weights Bc Br epoch time j i count copied rowCount hc hr left right innerCount appendCount ha≤
      profile model W k Qv a weights Bc Br := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  intro left right ha
  exact actual model W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br hWeights epoch time he ht
    j i count copied rowCount hc hr left right innerCount appendCount ha

theorem retained_first_trajectory {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (innerCount appendCount : ℕ)
    (ha : appendCount≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
      window model W k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr left right innerCount appendCount ha≤
        GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+profile model W k Qv a weights Bc Br :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (actual model W k Qv a weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr left right innerCount appendCount ha)

end Blotto.GeneralPaperSourceControllerContextStorage
