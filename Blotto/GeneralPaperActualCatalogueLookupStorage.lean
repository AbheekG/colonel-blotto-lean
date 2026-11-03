import Blotto.GeneralPaperLeastValidStorage

/-! The actual clipped native partition discharges every lookup endpoint
cap. Complete callback storage coexists with the retained partition, source
front/materialized/Shared/epoch data and the first completed trajectory. -/
namespace Blotto.GeneralPaperActualCatalogueLookupStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem catalogue {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summary : FixedArrayTable n ℕ) :
    let p := (GeneralPaperCataloguePartitionPrice.run true (fun w => w) model.rat W (8*a.C) summary).1
    ∀ i : Fin p.count,GeneralPaperLeastValidStorage.cellWindow model W a response
      (p.intervals.read i).1 (p.intervals.read i).2≤GeneralPaperLeastValidStorage.cellProfile model W a := by
  dsimp only
  intro i
  have h := GeneralPaperActualCellCatalogue.endpoints_bound true (fun w => w) model.rat W (8*a.C) summary i
  exact GeneralPaperLeastValidStorage.cell_bound model W a response _ _ h.1 h.2

theorem catalogue_compact {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summary : FixedArrayTable n ℕ) :
    let p := (GeneralPaperCataloguePartitionPrice.run true (fun w => w) model.rat W (8*a.C) summary).1
    ∀ i : Fin p.count,GeneralPaperLeastValidStorage.cellWindow model W a response
      (p.intervals.read i).1 (p.intervals.read i).2≤
      1073741824*(a.lambda+3)*(GeneralPaperDecoderControls.controlWord W a.lambda+
        model.rat (GeneralPaperDecoderControls.operandWidth a.lambda)) := by
  dsimp only
  intro i
  exact (catalogue model W a response summary i).trans (GeneralPaperLeastValidStorage.cell_profile_bound model W a)

theorem with_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (response : Bool) (learner : Learner) (j : Fin m) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    let p := (GeneralPaperCataloguePartitionPrice.run true (fun w => w) model.rat W (8*a.C) (summary learner cache j)).1
    ∀ i : Fin p.count,
    (GeneralPaperClassifierResultStorage.frontFootprint W r.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)+64*W)+
      GeneralPaperEncodedPartitionStorage.footprint W p+
      GeneralPaperLeastValidStorage.cellWindow model W a response (p.intervals.read i).1 (p.intervals.read i).2≤
      GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
        GeneralPaperEncodedPartitionStorage.profile W (64+8*a.lambda) ((GeneralPaperSourceParameters.prepare k).summarySize+1)+
        1073741824*(a.lambda+3)*(GeneralPaperDecoderControls.controlWord W a.lambda+
          model.rat (GeneralPaperDecoderControls.operandWidth a.lambda)) := by
  dsimp only
  intro i
  exact Nat.add_le_add (Nat.add_le_add
    (GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br epoch time he ht)
    (GeneralPaperCataloguePartitionStorage.source_returned model W _ _))
    (catalogue_compact model W _ response _ i)

theorem with_first_trajectory {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (response : Bool) (learner : Learner) (j : Fin m) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let first := prepare a k Qv weights firstBc firstBr
    let trees := treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    let p := (GeneralPaperCataloguePartitionPrice.run true (fun w => w) model.rat W (8*a.C) (summary learner cache j)).1
    ∀ i : Fin p.count,
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows
      (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
      ((GeneralPaperClassifierResultStorage.frontFootprint W r.1.1+
        (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
          GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)+64*W)+
        GeneralPaperEncodedPartitionStorage.footprint W p+
        GeneralPaperLeastValidStorage.cellWindow model W a response (p.intervals.read i).1 (p.intervals.read i).2)≤
      GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+
        (GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
          GeneralPaperEncodedPartitionStorage.profile W (64+8*a.lambda) ((GeneralPaperSourceParameters.prepare k).summarySize+1)+
          1073741824*(a.lambda+3)*(GeneralPaperDecoderControls.controlWord W a.lambda+
            model.rat (GeneralPaperDecoderControls.operandWidth a.lambda))) := by
  dsimp only
  intro i
  have h := GeneralPaperEncodedTrajectoryStorage.actual W k Qv
    (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1.1.1.1.2 weights firstBc firstBr _ (Nat.le_refl _)
  exact Nat.add_le_add h (with_residents model W k Qv b hb weights Bc Br epoch time he ht response learner j i)

end Blotto.GeneralPaperActualCatalogueLookupStorage
