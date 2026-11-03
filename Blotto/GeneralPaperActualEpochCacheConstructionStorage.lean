import Blotto.GeneralPaperEpochCacheConstructionStorage

/-! Actual generated/epoch/prepared-source callers supply all native
epoch-cache inputs and field-family option metadata. Full constructor and
field-row context coexist with the actual retained source residents. -/
namespace Blotto.GeneralPaperActualEpochCacheConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def arraysOfCache {m k : ℕ} (cache : GeneralPaperCatalogueEpochCache.Cache m k) : GeneralPaperFourSummaryArrays.Arrays m k :=
  ⟨cache.p,cache.q,cache.lambda,cache.mu⟩

theorem cache_arrays_valid {m k : ℕ} (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (hc : GeneralPaperCatalogueEpochMetadata.CodesValid cache) :
    GeneralPaperEpochCacheConstructionStorage.ValidFour cache.alphabet (arraysOfCache cache) :=
  ⟨hc .p,hc .q,hc .lambda,hc .mu⟩

theorem generated {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (trees : Trees m a.lambda) (hv : Valid a k trees) (hp : Paths a k trees)
    (count rowCount tailCount : ℕ) (hcount : count≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (htail : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    GeneralPaperEpochCacheConstructionStorage.window model W (GeneralPaperSourceParameters.prepare k).meshDenominator a arrays rfl
      count rowCount tailCount hcount hrow htail j i q≤
      GeneralPaperEpochCacheConstructionStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a := by
  dsimp only
  apply GeneralPaperEpochCacheConstructionStorage.bounded model W _ a _ rfl _ count rowCount tailCount hcount hrow htail j i q
  exact GeneralPaperActualOccurrencePreparation.four_codes true (fun w => w) model.rat W m k Qv a c hc
    (GeneralPaperQuantileComparison.width a.lambda k) trees hv hp _ rfl

theorem epoch {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (count rowCount tailCount : ℕ) (hcount : count≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (htail : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    GeneralPaperEpochCacheConstructionStorage.window model W (GeneralPaperSourceParameters.prepare k).meshDenominator a arrays rfl
      count rowCount tailCount hcount hrow htail j i q≤
      GeneralPaperEpochCacheConstructionStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a :=
  generated model W k Qv a c hc _ (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) count rowCount tailCount hcount hrow htail j i q

theorem prepared_inputs {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    let arrays := arraysOfCache cache
    GeneralPaperFieldFamilyConstructionStorage.ValidInputs a arrays
      (GeneralPaperEpochCacheConstructionStorage.candidate model W (GeneralPaperSourceParameters.prepare k).meshDenominator a arrays rfl).data.codes
      (GeneralPaperEpochCacheConstructionStorage.response model W (GeneralPaperSourceParameters.prepare k).meshDenominator a arrays rfl).data.codes := by
  dsimp only
  apply GeneralPaperEpochCacheConstructionStorage.inputs_valid model W _ _ _ rfl
  exact cache_arrays_valid _ (GeneralPaperCatalogueTreeCache.codes_valid _ _ _ _ _)

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (count rowCount tailCount : ℕ) (hcount : count≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (htail : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    GeneralPaperEpochCacheConstructionStorage.window model W (GeneralPaperSourceParameters.prepare k).meshDenominator a (arraysOfCache cache) rfl
      count rowCount tailCount hcount hrow htail j i q≤
      GeneralPaperEpochCacheConstructionStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a := by
  dsimp only
  apply GeneralPaperEpochCacheConstructionStorage.bounded model W _ _ _ rfl _ count rowCount tailCount hcount hrow htail j i q
  exact cache_arrays_valid _ (GeneralPaperCatalogueTreeCache.codes_valid _ _ _ _ _)

theorem with_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (count rowCount tailCount : ℕ) (hcount : count≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (htail : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    (GeneralPaperClassifierResultStorage.frontFootprint W r.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)+64*W)+
      GeneralPaperEpochCacheConstructionStorage.window model W (GeneralPaperSourceParameters.prepare k).meshDenominator a (arraysOfCache cache) rfl
        count rowCount tailCount hcount hrow htail j i q≤
      GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
        GeneralPaperEpochCacheConstructionStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a :=
  Nat.add_le_add (GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br epoch time he ht)
    (prepared model W k Qv b weights Bc Br epoch count rowCount tailCount hcount hrow htail j i q)

end Blotto.GeneralPaperActualEpochCacheConstructionStorage
