import Blotto.GeneralPaperCataloguePartitionStorage

/-! Catalogue partitions at actual generated source summaries and prepared
source/epoch residents. Code caps come from native quantile/cache metadata;
no supplied breakpoint/partition capacity or space oracle is used. -/
namespace Blotto.GeneralPaperActualPartitionStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem cache_bounded {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (ha : cache.alphabet=a)
    (hCodes : GeneralPaperCatalogueEpochMetadata.CodesValid cache)
    (learner : Learner) (j : Fin m) (used copied count : ℕ)
    (hc : count≤(GeneralPaperTailCataloguePartition.prepare (8*a.C) (summary learner cache j)).count) :
    GeneralPaperCataloguePartitionStorage.window model W (8*a.C) used copied count (summary learner cache j) hc≤
      GeneralPaperCataloguePartitionStorage.profile model W (8*a.C) (GeneralPaperSourceParameters.prepare k).summarySize := by
  apply GeneralPaperCataloguePartitionStorage.bounded model W (8*a.C) used copied count _ hc
  intro r
  have h := hCodes learner j r
  have hw : GeneralPaperCatalogueEpochMetadata.width learner cache≤2*(8*a.C) := by
    rw [←ha]
    cases learner <;> dsimp only [GeneralPaperCatalogueEpochMetadata.width] <;> omega
  exact h.trans_le hw

theorem tree_cache {m : ℕ} (model : RationalCostModel) (W k : ℕ) (a : Alphabet)
    (powers : GeneralPaperPreparedPowers.Prepared) (digits : ℕ) (trees : Trees m a.lambda)
    (learner : Learner) (j : Fin m) (used copied count : ℕ) :
    let cache := GeneralPaperCatalogueTreeCache.prepare powers digits a k trees
    ∀ hc : count≤(GeneralPaperTailCataloguePartition.prepare (8*a.C) (summary learner cache j)).count,
    GeneralPaperCataloguePartitionStorage.window model W (8*a.C) used copied count (summary learner cache j) hc≤
      GeneralPaperCataloguePartitionStorage.profile model W (8*a.C) (GeneralPaperSourceParameters.prepare k).summarySize := by
  dsimp only
  intro hc
  exact cache_bounded model W a _ rfl (GeneralPaperCatalogueTreeCache.codes_valid powers digits a k trees)
    learner j used copied count hc

theorem generated {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (trees : Trees m a.lambda) (hv : Valid a k trees) (hp : Paths a k trees)
    (learner : Learner) (j : Fin m) (used copied count : ℕ) :
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    ∀ hcount : count≤(GeneralPaperTailCataloguePartition.prepare (8*a.C) (summary learner cache j)).count,
    GeneralPaperCataloguePartitionStorage.window model W (8*a.C) used copied count (summary learner cache j) hcount≤
      GeneralPaperCataloguePartitionStorage.profile model W (8*a.C) (GeneralPaperSourceParameters.prepare k).summarySize := by
  dsimp only
  intro hcount
  exact cache_bounded model W a _ rfl
    (GeneralPaperSourceRankCache.codes true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees hv hp) learner j used copied count hcount

theorem epoch {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (learner : Learner) (j : Fin m) (used copied count : ℕ) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    ∀ hcount : count≤(GeneralPaperTailCataloguePartition.prepare (8*a.C) (summary learner cache j)).count,
    GeneralPaperCataloguePartitionStorage.window model W (8*a.C) used copied count (summary learner cache j) hcount≤
      GeneralPaperCataloguePartitionStorage.profile model W (8*a.C) (GeneralPaperSourceParameters.prepare k).summarySize :=
  generated model W k Qv a c hc _ (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) learner j used copied count

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (learner : Learner) (j : Fin m) (used copied count : ℕ) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let trees := treesAt ready.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare ready.2.source.powers ready.1.2.wordWidth a k trees
    ∀ hcount : count≤(GeneralPaperTailCataloguePartition.prepare (8*a.C) (summary learner cache j)).count,
    GeneralPaperCataloguePartitionStorage.window model W (8*a.C) used copied count (summary learner cache j) hcount≤
      GeneralPaperCataloguePartitionStorage.profile model W (8*a.C) (GeneralPaperSourceParameters.prepare k).summarySize := by
  dsimp only
  exact tree_cache model W k _ _ _ _ learner j used copied count

theorem with_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (learner : Learner) (j : Fin m) (used copied count : ℕ) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    ∀ hcount : count≤(GeneralPaperTailCataloguePartition.prepare (8*a.C) (summary learner cache j)).count,
    (GeneralPaperClassifierResultStorage.frontFootprint W r.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)+64*W)+
      GeneralPaperCataloguePartitionStorage.window model W (8*a.C) used copied count (summary learner cache j) hcount≤
      GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
        GeneralPaperCataloguePartitionStorage.profile model W (8*a.C) (GeneralPaperSourceParameters.prepare k).summarySize := by
  dsimp only
  intro hcount
  exact Nat.add_le_add (GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br epoch time he ht)
    (prepared model W k Qv b weights Bc Br epoch learner j used copied count hcount)

end Blotto.GeneralPaperActualPartitionStorage
