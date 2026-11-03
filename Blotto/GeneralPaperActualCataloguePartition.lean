import Blotto.GeneralPaperCataloguePartitionPrice

/-! Generated signed summaries and actual epoch forests supply the source
partition's strict code caps and ordering. Cellwise signed objective values
remain constant for every current retained prefix array throughout the epoch.
-/
namespace Blotto.GeneralPaperActualCataloguePartition
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperCatalogueOptionPlans (signed)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem generated_codes (bits : Bool) (index primitive : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hArrays : arrays=(GeneralPaperFourSummaryArrays.run bits index primitive W m k Qv a c hc digits trees).1)
    (response : Bool) (field : Fin m) : ∀ r,((signed response arrays).read field).read r<2*(8*a.C) := by
  subst arrays
  have hCodes := GeneralPaperSourceRankCache.codes bits index primitive W m k Qv a c hc digits trees hValid hPaths
  cases response
  · exact fun r => hCodes .lambda field r
  · exact fun r => hCodes .mu field r

theorem generated_ordered (bits : Bool) (index primitive : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (hDigits : digits=GeneralPaperQuantileComparison.width a.lambda k)
    (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hArrays : arrays=(GeneralPaperFourSummaryArrays.run bits index primitive W m k Qv a c hc digits trees).1)
    (response : Bool) (field : Fin m) : Monotone ((signed response arrays).read field).read := by
  have hOrdered : GeneralPaperCatalogueEpochMetadata.Ordered
      (GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu) := by
    rw [hArrays,GeneralPaperFourSummaryArrays.epoch_cache_data bits index primitive W m k Qv a c hc digits trees hValid hPaths,hc,hDigits]
    exact GeneralPaperCatalogueTreeCache.ordered a k trees hValid hPaths
  cases response
  · exact hOrdered .lambda field
  · exact hOrdered .mu field

theorem generated_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hArrays : arrays=(GeneralPaperFourSummaryArrays.run true (fun w => w) primitive W m k Qv a c hc digits trees).1)
    (response : Bool) (field : Fin m) :
    (GeneralPaperCataloguePartitionPrice.run true (fun w => w) primitive W (8*a.C) ((signed response arrays).read field)).2≤
      GeneralPaperCataloguePartitionPrice.profile primitive W (GeneralPaperSourceParameters.prepare k).summarySize (8*a.C) :=
  GeneralPaperCataloguePartitionPrice.bit_work primitive hMono W (8*a.C) ((signed response arrays).read field)
    (generated_codes true (fun w => w) primitive W m k Qv a c hc digits trees hValid hPaths arrays hArrays response field)

theorem epoch_work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (response : Bool) (field : Fin m) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) primitive W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    (GeneralPaperCataloguePartitionPrice.run true (fun w => w) primitive W (8*a.C) ((signed response arrays).read field)).2≤
      GeneralPaperCataloguePartitionPrice.profile primitive W (GeneralPaperSourceParameters.prepare k).summarySize (8*a.C) :=
  generated_work primitive hMono W m k Qv a c hc _ _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) _ rfl response field

theorem signed_value_constant (bits : Bool) (index primitive : ℕ → ℕ) (W k U : ℕ) (summary : Summary k)
    (preparedPrefix : Prefix k) (hMono : Monotone summary.read) (hCodes : ∀ r,summary.read r<2*U)
    (r : Fin (GeneralPaperCataloguePartitionPrice.run bits index primitive W U summary).1.count) (i j : ℕ)
    (hI : GeneralPaperEpochCellInstructions.Contains (GeneralPaperCataloguePartitionPrice.run bits index primitive W U summary).1.intervals r i)
    (hJ : GeneralPaperEpochCellInstructions.Contains (GeneralPaperCataloguePartitionPrice.run bits index primitive W U summary).1.intervals r j) :
    GeneralPaperSignedTailProperties.signedValue k U summary preparedPrefix i=
      GeneralPaperSignedTailProperties.signedValue k U summary preparedPrefix j := by
  have inherit (p : GeneralPaperPreparedPartition.Prepared) (hp : p=GeneralPaperTailCataloguePartition.prepare U summary)
      (cell : Fin p.count) (x y : ℕ) (hx : GeneralPaperEpochCellInstructions.Contains p.intervals cell x)
      (hy : GeneralPaperEpochCellInstructions.Contains p.intervals cell y) :
      GeneralPaperSignedTailProperties.signedValue k U summary preparedPrefix x=
        GeneralPaperSignedTailProperties.signedValue k U summary preparedPrefix y := by
    subst p
    exact GeneralPaperTailCataloguePartition.signed_value_constant k U summary preparedPrefix hMono hCodes cell x y hx hy
  exact inherit _ (GeneralPaperCataloguePartitionPrice.data bits index primitive W U summary) r i j hI hJ

theorem generated_constant (bits : Bool) (index primitive : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (hDigits : digits=GeneralPaperQuantileComparison.width a.lambda k)
    (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hArrays : arrays=(GeneralPaperFourSummaryArrays.run bits index primitive W m k Qv a c hc digits trees).1)
    (response : Bool) (field : Fin m) (preparedPrefix : Prefix k)
    (r : Fin (GeneralPaperCataloguePartitionPrice.run bits index primitive W (8*a.C) ((signed response arrays).read field)).1.count)
    (i j : ℕ)
    (hI : GeneralPaperEpochCellInstructions.Contains
      (GeneralPaperCataloguePartitionPrice.run bits index primitive W (8*a.C) ((signed response arrays).read field)).1.intervals r i)
    (hJ : GeneralPaperEpochCellInstructions.Contains
      (GeneralPaperCataloguePartitionPrice.run bits index primitive W (8*a.C) ((signed response arrays).read field)).1.intervals r j) :
    GeneralPaperSignedTailProperties.signedValue k (8*a.C) ((signed response arrays).read field) preparedPrefix i=
      GeneralPaperSignedTailProperties.signedValue k (8*a.C) ((signed response arrays).read field) preparedPrefix j :=
  signed_value_constant bits index primitive W k (8*a.C) ((signed response arrays).read field) preparedPrefix
    (generated_ordered bits index primitive W m k Qv a c hc digits hDigits trees hValid hPaths arrays hArrays response field)
    (generated_codes bits index primitive W m k Qv a c hc digits trees hValid hPaths arrays hArrays response field) r i j hI hJ

theorem point_width (a : Alphabet) : GeneralPaperCataloguePointOperands.width (8*a.C)≤192+32*a.lambda := by
  rw [a.dyadic]
  have h := GeneralPaperSourceRankCache.code_word a.lambda
  unfold GeneralPaperCataloguePointOperands.width
  omega

theorem summary_cell_width (k : ℕ) :
    GeneralPaperBoundaryCellPrice.width ((GeneralPaperSourceParameters.prepare k).summarySize+2)≤1024+32*k := by
  have hs := (GeneralPaperSourceParameters.data k).2.2.2.2.2
  have hp := GeneralPaperNatPowerOperands.power_width 2 (34+k)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (2^(34+k)) 4
  have h2 : binaryWordWidth 2=2 := by decide
  have h4 : binaryWordWidth 4=3 := by decide
  rw [h2] at hp
  unfold GeneralPaperBoundaryCellPrice.width
  rw [hs]
  change 64+8*binaryWordWidth (2^(34+k)+4)≤1024+32*k
  omega

end Blotto.GeneralPaperActualCataloguePartition
