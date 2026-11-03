import Blotto.GeneralPaperQueryLossConstructionStorage

/-! Native partition representatives and actual source occurrence arrays
discharge every rank-plan query premise. All-prefix certificates are erased
propositions; no supplied space/capacity/height oracle enters the algorithm. -/
namespace Blotto.GeneralPaperActualRankPlanConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem unsigned_representatives {m : ℕ} (model : RationalCostModel) (W k U : ℕ)
    (cdfSummary tailSummary : Summary k) (options : FixedArrayTable m ℕ) :
    let part := (GeneralPaperUnsignedCellPartitionPrice.run true (fun w => w) model.rat W U cdfSummary tailSummary options).1
    ∀ count (hc : count≤part.count), GeneralPaperRankCutArrayStorage.representativeWindow model W U part.intervals count hc≤
      GeneralPaperRankCutArrayStorage.representativeProfile model W U part.count := by
  dsimp only
  intro count hc
  apply GeneralPaperRankCutArrayStorage.representative_bound model W U _ _ count hc
  exact GeneralPaperEpochPartitionPrice.cell_bounds true (fun w => w) model.rat W U cdfSummary
    (GeneralPaperUnsignedCellInputPrice.run true (fun w => w) model.rat W U tailSummary options).1.1

theorem signed_representatives {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ) :
    let part := (GeneralPaperSignedCellPartitionPrice.run true (fun w => w) model.rat W U summary options).1
    ∀ count (hc : count≤part.count), GeneralPaperRankCutArrayStorage.representativeWindow model W (2*U) part.intervals count hc≤
      GeneralPaperRankCutArrayStorage.representativeProfile model W (2*U) part.count := by
  dsimp only
  intro count hc
  apply GeneralPaperRankCutArrayStorage.representative_bound model W (2*U) _ _ count hc
  exact GeneralPaperEpochPartitionPrice.cell_bounds true (fun w => w) model.rat W (2*U)
    (GeneralPaperSignedCellPositionsPrice.run true (fun w => w) model.rat W U summary).1.1
    (GeneralPaperSignedCellExtrasPrice.run true (fun w => w) model.rat W U options).1.1

theorem unsigned_cell_ranks {m : ℕ} (model : RationalCostModel) (W k U : ℕ)
    (cdfSummary tailSummary : Summary k) (options : FixedArrayTable m ℕ)
    (hCDF : ∀ i,cdfSummary.read i≤U) (hTail : ∀ i,tailSummary.read i≤2*U) :
    let part := (GeneralPaperUnsignedCellPartitionPrice.run true (fun w => w) model.rat W U cdfSummary tailSummary options).1
    let queries := (GeneralPaperCellRepresentativePrice.run true (fun w => w) model.rat W part.intervals).1.1
    ∀ cdfCount tailCount (hc : cdfCount≤part.count) (ht : tailCount≤part.count+1) (q : Fin (part.count+1)),
      GeneralPaperQueryLossConstructionStorage.window model W k U cdfSummary tailSummary queries cdfCount tailCount hc ht q≤
        GeneralPaperQueryLossConstructionStorage.profile model W part.count k U := by
  dsimp only
  intro cdfCount tailCount hc ht q
  exact GeneralPaperQueryLossConstructionStorage.bounded model W k U cdfSummary tailSummary _ hCDF hTail
    (GeneralPaperUnsignedCellPartitionPrice.representative_codes true (fun w => w) model.rat W U cdfSummary tailSummary options)
    cdfCount tailCount hc ht q

theorem signed_cell_ranks {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ)
    (hSummary : ∀ i,summary.read i≤U) :
    let part := (GeneralPaperSignedCellPartitionPrice.run true (fun w => w) model.rat W U summary options).1
    let queries := (GeneralPaperCellRepresentativePrice.run true (fun w => w) model.rat W part.intervals).1.1
    ∀ count (hc : count≤part.count), GeneralPaperSignedUpdateConstructionStorage.window model W k U summary queries count hc≤
      GeneralPaperSignedUpdateConstructionStorage.profile model W part.count k U := by
  dsimp only
  intro count hc
  exact GeneralPaperSignedUpdateConstructionStorage.bounded model W k U summary _ hSummary
    (GeneralPaperSignedCellPartitionPrice.representative_codes true (fun w => w) model.rat W U summary options) count hc

def Certified (model : RationalCostModel) (W k U : ℕ) (own opposite signedSummary : Summary k) : Prop :=
  let n := (GeneralPaperSourceParameters.prepare k).summarySize
  (∀ cdfCount tailCount (hc : cdfCount≤n) (ht : tailCount≤n+1) (q : Fin (n+1)),
    GeneralPaperQueryLossConstructionStorage.window model W k U opposite signedSummary own cdfCount tailCount hc ht q≤
      GeneralPaperQueryLossConstructionStorage.profile model W n k U) ∧
  (∀ count (hc : count≤n), GeneralPaperSignedUpdateConstructionStorage.window model W k U own signedSummary count hc≤
    GeneralPaperSignedUpdateConstructionStorage.profile model W n k U)

theorem certified (model : RationalCostModel) (W k U : ℕ) (own opposite signedSummary : Summary k)
    (hown : ∀ i,own.read i<U) (hop : ∀ i,opposite.read i<U) (hs : ∀ i,signedSummary.read i<2*U) :
    Certified model W k U own opposite signedSummary := by
  constructor
  · intro cdfCount tailCount hc ht q
    exact GeneralPaperQueryLossConstructionStorage.bounded model W k U opposite signedSummary own
      (fun i => (hop i).le) (fun i => (hs i).le) hown cdfCount tailCount hc ht q
  · intro count hc
    exact GeneralPaperSignedUpdateConstructionStorage.bounded model W k U own signedSummary (fun i => (hown i).le) hs count hc

theorem cache {m k : ℕ} (model : RationalCostModel) (W : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (hv : GeneralPaperCatalogueEpochMetadata.CodesValid cache) (response : Bool) (j : Fin m) :
    let own := (if response then cache.q else cache.p).read j
    let opposite := (if response then cache.p else cache.q).read j
    let signedSummary := (if response then cache.mu else cache.lambda).read j
    Certified model W k (8*cache.alphabet.C) own opposite signedSummary := by
  cases response
  · exact certified model W k (8*cache.alphabet.C) _ _ _ (hv .p j) (hv .q j) (hv .lambda j)
  · exact certified model W k (8*cache.alphabet.C) _ _ _ (hv .q j) (hv .p j) (hv .mu j)

theorem generated {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (trees : Trees m a.lambda) (hv : Valid a k trees) (hp : Paths a k trees) (response : Bool) (j : Fin m) :
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    let own := (if response then cache.q else cache.p).read j
    let opposite := (if response then cache.p else cache.q).read j
    let signedSummary := (if response then cache.mu else cache.lambda).read j
    Certified model W k (8*a.C) own opposite signedSummary := by
  dsimp only
  let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
    (GeneralPaperQuantileComparison.width a.lambda k) trees).1
  apply cache model W (GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu) _ response j
  intro learner field r
  cases learner
  · exact GeneralPaperSourceRankCache.codes true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees hv hp .p field r
  · exact GeneralPaperSourceRankCache.codes true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees hv hp .q field r
  · exact GeneralPaperSourceRankCache.codes true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees hv hp .lambda field r
  · exact GeneralPaperSourceRankCache.codes true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees hv hp .mu field r

theorem epoch {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (response : Bool) (j : Fin m) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    let own := (if response then cache.q else cache.p).read j
    let opposite := (if response then cache.p else cache.q).read j
    let signedSummary := (if response then cache.mu else cache.lambda).read j
    Certified model W k (8*a.C) own opposite signedSummary :=
  generated model W k Qv a c hc _ (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) response j

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (response : Bool) (j : Fin m) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    let own := (if response then cache.q else cache.p).read j
    let opposite := (if response then cache.p else cache.q).read j
    let signedSummary := (if response then cache.mu else cache.lambda).read j
    Certified model W k (8*a.C) own opposite signedSummary :=
  cache model W _ (GeneralPaperCatalogueTreeCache.codes_valid _ _ _ _ _) response j

theorem with_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (response : Bool) (j : Fin m) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    let own := (if response then cache.q else cache.p).read j
    let opposite := (if response then cache.p else cache.q).read j
    let signedSummary := (if response then cache.mu else cache.lambda).read j
    let n := (GeneralPaperSourceParameters.prepare k).summarySize
    ∀ cdfCount tailCount signedCount (hc : cdfCount≤n) (htail : tailCount≤n+1) (hs : signedCount≤n) (q : Fin (n+1)),
    (GeneralPaperClassifierResultStorage.frontFootprint W r.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)+64*W)+
      GeneralPaperQueryLossConstructionStorage.window model W k (8*a.C) opposite signedSummary own cdfCount tailCount hc htail q+
      GeneralPaperSignedUpdateConstructionStorage.window model W k (8*a.C) own signedSummary signedCount hs≤
      GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
        GeneralPaperQueryLossConstructionStorage.profile model W n k (8*a.C)+GeneralPaperSignedUpdateConstructionStorage.profile model W n k (8*a.C) := by
  have hcert := prepared model W k Qv b weights Bc Br epoch response j
  have hr := GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br epoch time he ht
  dsimp only at hcert ⊢
  intro cdfCount tailCount signedCount hc htail hs q
  exact Nat.add_le_add (Nat.add_le_add hr (hcert.1 cdfCount tailCount hc htail q)) (hcert.2 signedCount hs)

end Blotto.GeneralPaperActualRankPlanConstructionStorage
