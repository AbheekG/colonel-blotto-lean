import Blotto.GeneralPaperCatalogueArrayConstructionStorage

/-! Actual signed summary families supply the catalogue-array input caps.
The candidate/response branches use lambda/mu respectively, at generated
four-summary data, actual epochs and the prepared source cache. -/
namespace Blotto.GeneralPaperActualCatalogueArrayStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop
open GeneralPaperCatalogueProjection (Field)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem generated {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (trees : Trees m a.lambda) (hv : Valid a k trees) (hp : Paths a k trees) (response : Bool)
    (field : Field) (count copied rowCount : ℕ) (hcount : count≤m) (hcopied : copied≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (j : Fin m) :
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let inputs := if response then arrays.mu else arrays.lambda
    GeneralPaperCatalogueArrayConstructionStorage.window model W a response inputs field count copied rowCount hcount hcopied hrow j≤
      GeneralPaperCatalogueArrayConstructionStorage.profile model W m (GeneralPaperSourceParameters.prepare k).summarySize a := by
  dsimp only
  apply GeneralPaperCatalogueArrayConstructionStorage.bounded model W a response _ _ field count copied rowCount hcount hcopied hrow j
  intro fieldIndex r
  cases response
  · exact GeneralPaperSourceRankCache.codes true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees hv hp .lambda fieldIndex r
  · exact GeneralPaperSourceRankCache.codes true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees hv hp .mu fieldIndex r

theorem epoch {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (response : Bool)
    (field : Field) (count copied rowCount : ℕ) (hcount : count≤m) (hcopied : copied≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (j : Fin m) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let inputs := if response then arrays.mu else arrays.lambda
    GeneralPaperCatalogueArrayConstructionStorage.window model W a response inputs field count copied rowCount hcount hcopied hrow j≤
      GeneralPaperCatalogueArrayConstructionStorage.profile model W m (GeneralPaperSourceParameters.prepare k).summarySize a :=
  generated model W k Qv a c hc _ (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) response field count copied rowCount hcount hcopied hrow j

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (response : Bool)
    (field : Field) (count copied rowCount : ℕ) (hcount : count≤m) (hcopied : copied≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (j : Fin m) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let trees := treesAt ready.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare ready.2.source.powers ready.1.2.wordWidth a k trees
    let inputs := if response then cache.mu else cache.lambda
    GeneralPaperCatalogueArrayConstructionStorage.window model W a response inputs field count copied rowCount hcount hcopied hrow j≤
      GeneralPaperCatalogueArrayConstructionStorage.profile model W m (GeneralPaperSourceParameters.prepare k).summarySize a := by
  dsimp only
  apply GeneralPaperCatalogueArrayConstructionStorage.bounded model W _ response _ _ field count copied rowCount hcount hcopied hrow j
  intro fieldIndex r
  cases response
  · exact GeneralPaperCatalogueTreeCache.codes_valid _ _ _ k _ .lambda fieldIndex r
  · exact GeneralPaperCatalogueTreeCache.codes_valid _ _ _ k _ .mu fieldIndex r

theorem with_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (response : Bool) (field : Field) (count copied rowCount : ℕ) (hcount : count≤m) (hcopied : copied≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (j : Fin m) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    let inputs := if response then cache.mu else cache.lambda
    (GeneralPaperClassifierResultStorage.frontFootprint W r.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)+64*W)+
      GeneralPaperCatalogueArrayConstructionStorage.window model W a response inputs field count copied rowCount hcount hcopied hrow j≤
      GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
        GeneralPaperCatalogueArrayConstructionStorage.profile model W m (GeneralPaperSourceParameters.prepare k).summarySize a :=
  Nat.add_le_add (GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br epoch time he ht)
    (prepared model W k Qv b weights Bc Br epoch response field count copied rowCount hcount hcopied hrow j)

end Blotto.GeneralPaperActualCatalogueArrayStorage
