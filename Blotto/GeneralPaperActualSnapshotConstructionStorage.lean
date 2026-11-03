import Blotto.GeneralPaperSnapshotFamilyConstructionStorage
import Blotto.GeneralPaperActualEpochParentStorage

/-! Actual reached source states derive every snapshot-constructor premise.
The native family constructor joins the source/controller/selector context,
prepared residents and a retained first trajectory, without source replay.
The bounds include terminal local times and empty/finished fill prefixes. -/
namespace Blotto.GeneralPaperActualSnapshotConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperCatalogueEpochRun
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem selected {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time count innerCount used copied : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (hn : count≤m) (hi : innerCount≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    GeneralPaperSnapshotFamilyConstructionStorage.window model W c (stateAt (selected cache Qv weights Bc Br) time).fields
      count innerCount used copied hn hi≤GeneralPaperSnapshotFamilyConstructionStorage.profile model W m cache.alphabet.lambda k Qv :=
  GeneralPaperSnapshotFamilyConstructionStorage.bounded model W cache.alphabet.lambda Qv c hc _
    (GeneralPaperActualEpochSnapshotPrice.selected_fields cache Qv c hc weights Bc Br time ht)
    (fun j => GeneralPaperEncodedEpochLevels.actual_counts cache _ j ((stateAt _ time).plan_spec j))
    count innerCount used copied hn hi

theorem actual {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time count innerCount used copied : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (hn : count≤m) (hi : innerCount≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    let shared := prepare a k Qv weights Bc Br
    let current := epochRun shared a k (treesAt shared a k epoch)
    GeneralPaperSnapshotFamilyConstructionStorage.window model W c (stateAt current time).fields count innerCount used copied hn hi≤
      GeneralPaperSnapshotFamilyConstructionStorage.profile model W m a.lambda k Qv := by
  dsimp only
  rw [epochRun_selected]
  exact selected model W Qv _ c hc weights Bc Br time count innerCount used copied ht hn hi

theorem prepared_with_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time count innerCount used copied : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (hn : count≤m) (hi : innerCount≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let current := epochRun ready.1.2 a k (treesAt ready.1.2 a k epoch)
    (GeneralPaperClassifierResultStorage.frontFootprint W ready.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W ready.2+GeneralPaperEncodedSharedSource.footprint W ready.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)+64*W)+
      GeneralPaperSnapshotFamilyConstructionStorage.window model W ready.2.source (stateAt current time).fields count innerCount used copied hn hi≤
        GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
          GeneralPaperSnapshotFamilyConstructionStorage.profile model W m a.lambda k Qv := by
  have hbase := GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br epoch time he ht
  have hchild := actual model W k Qv (GeneralPaperProxyParameters.alphabet m k)
    (GeneralPaperMaterializedPowerCache.specification m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv) rfl
    weights Bc Br epoch time count innerCount used copied ht hn hi
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data] at hbase ⊢
  exact Nat.add_le_add hbase hchild

theorem with_source_context {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hn : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m)
    (left right : Fin (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size) (innerCount appendCount numCount : ℕ)
    (ha : appendCount≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (hi : numCount≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    let shared := prepare a k Qv weights Bc Br
    let current := epochRun shared a k (treesAt shared a k epoch)
    GeneralPaperSourceControllerContextStorage.window model W k Qv a shared weights Bc Br epoch time
      j i count copied rowCount hn hr left right innerCount appendCount ha+
      GeneralPaperSnapshotFamilyConstructionStorage.window model W c (stateAt current time).fields rowCount numCount innerCount copied hr hi≤
        GeneralPaperSourceControllerContextStorage.profile model W k Qv a weights Bc Br+
          GeneralPaperSnapshotFamilyConstructionStorage.profile model W m a.lambda k Qv :=
  Nat.add_le_add (GeneralPaperSourceControllerContextStorage.actual model W k Qv a weights Bc Br hw epoch time he ht
    j i count copied rowCount hn hr left right innerCount appendCount ha)
    (actual model W k Qv a c hc weights Bc Br epoch time rowCount numCount innerCount copied (by omega) hr hi)

theorem retained_first_trajectory {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (epoch time count innerCount used copied : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (hn : count≤m) (hi : innerCount≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    let first := prepare a k Qv weights firstBc firstBr
    let shared := prepare a k Qv weights Bc Br
    let current := epochRun shared a k (treesAt shared a k epoch)
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (execute first a k first.trajectory.epochs).2+
      GeneralPaperSnapshotFamilyConstructionStorage.window model W c (stateAt current time).fields count innerCount used copied hn hi≤
        GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+
          GeneralPaperSnapshotFamilyConstructionStorage.profile model W m a.lambda k Qv :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (actual model W k Qv a c hc weights Bc Br epoch time count innerCount used copied ht hn hi)

end Blotto.GeneralPaperActualSnapshotConstructionStorage
