import Blotto.GeneralPaperCellPartitionConstructionStorage

/-! Actual four-summary/Ready metadata supplies every field-partition
operand cap. The certificate quantifies over all native construction prefixes;
it is an erased proposition, never a source capacity/height/space oracle. -/
namespace Blotto.GeneralPaperActualFieldPartitionStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOptionPlans (signed)
open GeneralPaperCellPartitionConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def Certified {n m : ℕ} (model : RationalCostModel) (W U : ℕ)
    (own opposite signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) : Prop :=
  (∀ inputCount usedP usedE copied count (hi : inputCount≤n+m)
    (hc : count≤(GeneralPaperEpochPartition.prepare U opposite (unsignedExtras model W U signedSummary options)).count),
    unsignedWindow model W U inputCount usedP usedE copied count opposite signedSummary options hi hc≤unsignedProfile model W U n m) ∧
  (∀ positionCount extraCount usedP usedE copied count (hp : positionCount≤2*n) (he : extraCount≤2*m+1)
    (hc : count≤(GeneralPaperEpochPartition.prepare (2*U) (signedPositions model W U own) (signedExtras model W U options)).count),
    signedWindow model W U positionCount extraCount usedP usedE copied count own options hp he hc≤signedProfile model W U n m)

theorem certified {n m : ℕ} (model : RationalCostModel) (W U : ℕ)
    (own opposite signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (hown : ∀ r,own.read r<U) (hop : ∀ r,opposite.read r<U) (hs : ∀ r,signedSummary.read r<2*U) (ho : ∀ r,options.read r<U) :
    Certified model W U own opposite signedSummary options := by
  constructor
  · intro inputCount usedP usedE copied count hi hc
    exact unsigned_bounded model W U inputCount usedP usedE copied count opposite signedSummary options hop hs ho hi hc
  · intro positionCount extraCount usedP usedE copied count hp he hc
    exact signed_bounded model W U positionCount extraCount usedP usedE copied count own options hown ho hp he hc

theorem cache {m k : ℕ} (model : RationalCostModel) (W : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (hv : GeneralPaperCatalogueEpochMetadata.CodesValid cache) (response : Bool) (j : Fin m) :
    let own := (if response then cache.q else cache.p).read j
    let opposite := (if response then cache.p else cache.q).read j
    let signedSummary := (if response then cache.mu else cache.lambda).read j
    let ready := if response then cache.response else cache.candidate
    Certified model W (8*cache.alphabet.C) own opposite signedSummary (ready.data.codes.read j) := by
  cases response
  · apply certified model W (8*cache.alphabet.C) _ _ _ _ (hv .p j) (hv .q j) (hv .lambda j)
    intro i
    change (cache.candidate.data.codes.read j).read i<_
    rw [cache.candidate_spec]
    exact GeneralPaperCatalogueArrays.code_bound cache.alphabet false k cache.lambda j i
  · apply certified model W (8*cache.alphabet.C) _ _ _ _ (hv .q j) (hv .p j) (hv .mu j)
    intro i
    change (cache.response.data.codes.read j).read i<_
    rw [cache.response_spec]
    exact GeneralPaperCatalogueArrays.code_bound cache.alphabet true k cache.mu j i

theorem generated {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (trees : Trees m a.lambda) (hv : Valid a k trees) (hp : Paths a k trees) (response : Bool) (j : Fin m) :
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    let own := (if response then cache.q else cache.p).read j
    let opposite := (if response then cache.p else cache.q).read j
    let signedSummary := (if response then cache.mu else cache.lambda).read j
    let ready := if response then cache.response else cache.candidate
    Certified model W (8*a.C) own opposite signedSummary (ready.data.codes.read j) := by
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
    let ready := if response then cache.response else cache.candidate
    Certified model W (8*a.C) own opposite signedSummary (ready.data.codes.read j) :=
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
    let ready := if response then cache.response else cache.candidate
    Certified model W (8*a.C) own opposite signedSummary (ready.data.codes.read j) :=
  cache model W _ (GeneralPaperCatalogueTreeCache.codes_valid _ _ _ _ _) response j

theorem with_residents {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (hepoch : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (htime : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (response : Bool) (j : Fin m) :
    let r := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := r.1.1.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt r.1.2 a k epoch
    let cache := GeneralPaperCatalogueTreeCache.prepare r.2.source.powers r.1.2.wordWidth a k trees
    let own := (if response then cache.q else cache.p).read j
    let opposite := (if response then cache.p else cache.q).read j
    let signedSummary := (if response then cache.mu else cache.lambda).read j
    let ready := if response then cache.response else cache.candidate
    let options := ready.data.codes.read j
    let s := (GeneralPaperSourceParameters.prepare k).summarySize
    ∀ inputCount positionCount extraCount usedP usedE copied countU countS
      (hi : inputCount≤s+(s+2)) (hp : positionCount≤2*s) (he : extraCount≤2*(s+2)+1)
      (hu : countU≤(GeneralPaperEpochPartition.prepare (8*a.C) opposite (unsignedExtras model W (8*a.C) signedSummary options)).count)
      (hs : countS≤(GeneralPaperEpochPartition.prepare (2*(8*a.C)) (signedPositions model W (8*a.C) own)
        (signedExtras model W (8*a.C) options)).count),
    (GeneralPaperClassifierResultStorage.frontFootprint W r.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W r.2+GeneralPaperEncodedSharedSource.footprint W r.1.2+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)+64*W)+
      unsignedWindow model W (8*a.C) inputCount usedP usedE copied countU opposite signedSummary options hi hu+
      signedWindow model W (8*a.C) positionCount extraCount usedP usedE copied countS own options hp he hs≤
      GeneralPaperPrecallResidentStorage.residentProfile W k Qv a weights Bc Br+
        unsignedProfile model W (8*a.C) s (s+2)+signedProfile model W (8*a.C) s (s+2) := by
  have hc := prepared model W k Qv b weights Bc Br epoch response j
  have hr := GeneralPaperPrecallResidentStorage.prepared_resident model W k Qv b hb weights Bc Br epoch time hepoch htime
  dsimp only at hc ⊢
  intro inputCount positionCount extraCount usedP usedE copied countU countS hi hp he hu hs
  exact Nat.add_le_add (Nat.add_le_add hr (hc.1 inputCount usedP usedE copied countU hi hu))
    (hc.2 positionCount extraCount usedP usedE copied countS hp he hs)

end Blotto.GeneralPaperActualFieldPartitionStorage
