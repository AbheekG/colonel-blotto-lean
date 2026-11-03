import Blotto.GeneralPaperReadyConstructionStorage

/-! Actual generated and prepared signed summaries discharge every native Ready
input premise. Candidate/response branches reuse lambda/mu and retained
source residents; no tag, cut or rank payload oracle is introduced. -/
namespace Blotto.GeneralPaperActualReadyStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem generated {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (trees : Trees m a.lambda) (hv : Valid a k trees) (hp : Paths a k trees) (response : Bool)
    (count rowCount tailCount : ℕ) (hcount : count≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (htail : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let inputs := if response then arrays.mu else arrays.lambda
    GeneralPaperReadyConstructionStorage.window model W (GeneralPaperSourceParameters.prepare k).meshDenominator a response inputs rfl
      count rowCount tailCount hcount hrow htail j i q≤
      GeneralPaperReadyConstructionStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a := by
  dsimp only
  apply GeneralPaperReadyConstructionStorage.bounded model W _ a response _ rfl _ count rowCount tailCount hcount hrow htail j i q
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
    (count rowCount tailCount : ℕ) (hcount : count≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (htail : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let inputs := if response then arrays.mu else arrays.lambda
    GeneralPaperReadyConstructionStorage.window model W (GeneralPaperSourceParameters.prepare k).meshDenominator a response inputs rfl
      count rowCount tailCount hcount hrow htail j i q≤
      GeneralPaperReadyConstructionStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a :=
  generated model W k Qv a c hc _ (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) response count rowCount tailCount hcount hrow htail j i q

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (response : Bool)
    (count rowCount tailCount : ℕ) (hcount : count≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (htail : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let trees := treesAt ready.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare ready.2.source.powers ready.1.2.wordWidth a k trees
    let inputs := if response then cache.mu else cache.lambda
    GeneralPaperReadyConstructionStorage.window model W (GeneralPaperSourceParameters.prepare k).meshDenominator a response inputs rfl
      count rowCount tailCount hcount hrow htail j i q≤
      GeneralPaperReadyConstructionStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a := by
  dsimp only
  apply GeneralPaperReadyConstructionStorage.bounded model W _ _ response _ rfl _ count rowCount tailCount hcount hrow htail j i q
  intro fieldIndex r
  cases response
  · exact GeneralPaperCatalogueTreeCache.codes_valid _ _ _ k _ .lambda fieldIndex r
  · exact GeneralPaperCatalogueTreeCache.codes_valid _ _ _ k _ .mu fieldIndex r

theorem with_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (response : Bool) (count rowCount tailCount : ℕ) (hcount : count≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (htail : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    let inputs := if response then cache.mu else cache.lambda
    (GeneralPaperClassifierResultStorage.frontFootprint W r.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)+64*W)+
      GeneralPaperReadyConstructionStorage.window model W (GeneralPaperSourceParameters.prepare k).meshDenominator a response inputs rfl
      count rowCount tailCount hcount hrow htail j i q≤
      GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
        GeneralPaperReadyConstructionStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a :=
  Nat.add_le_add (GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br epoch time he ht)
    (prepared model W k Qv b weights Bc Br epoch response count rowCount tailCount hcount hrow htail j i q)

theorem retained_mesh {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1.2.source.controls.source.meshDenominator=
      (GeneralPaperSourceParameters.prepare k).meshDenominator := by
  rw [GeneralPaperPreparedSharedSource.data]
  rfl

theorem retained_prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (response : Bool)
    (count rowCount tailCount : ℕ) (hcount : count≤m)
    (hrow : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (htail : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    let inputs := if response then cache.mu else cache.lambda
    GeneralPaperReadyConstructionStorage.window model W r.2.source.controls.source.meshDenominator a response inputs
      (retained_mesh model k Qv b weights Bc Br) count rowCount tailCount hcount hrow htail j i q≤
      GeneralPaperReadyConstructionStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a := by
  dsimp only
  simp only [retained_mesh]
  exact prepared model W k Qv b weights Bc Br epoch response count rowCount tailCount hcount hrow htail j i q

end Blotto.GeneralPaperActualReadyStorage
