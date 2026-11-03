import Blotto.GeneralPaperSignedCellPartitionPrice

/-! Generated summaries and retained native optimizer entries supply the
complete unsigned/signed partition premises. Actual source slot counts
also bound every representative fill; no caller magnitude oracle is used.
-/
namespace Blotto.GeneralPaperActualCellPartitions
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOptionPlans (signed)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem option_codes {m k : ℕ} (a : Alphabet) (response : Bool) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (hReady : ready=GeneralPaperCatalogueOptimizer.prepare a response k (signed response arrays))
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    (ready.data.codes.read j).read i<8*a.C := by
  rw [hReady]
  exact GeneralPaperCatalogueArrays.code_bound a response k (signed response arrays) j i

theorem generated_work (bits : Bool) (index price : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hArrays : arrays=(GeneralPaperFourSummaryArrays.run bits index price W m k Qv a c hc digits trees).1)
    (model : RationalCostModel) (response : Bool) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (hReady : ready=GeneralPaperCatalogueOptimizer.prepare a response k (signed response arrays)) (j : Fin m) :
    let own := (if response then arrays.q else arrays.p).read j
    let opposite := (if response then arrays.p else arrays.q).read j
    let signedSummary := (signed response arrays).read j
    let options := ready.data.codes.read j
    let s := (GeneralPaperSourceParameters.prepare k).summarySize
    (GeneralPaperUnsignedCellPartitionPrice.run true (fun w => w) model.rat W (8*a.C) opposite signedSummary options).2≤
      GeneralPaperUnsignedCellPartitionPrice.profile model.rat W s (s+2) (8*a.C) ∧
    (GeneralPaperSignedCellPartitionPrice.run true (fun w => w) model.rat W (8*a.C) own options).2≤
      GeneralPaperSignedCellPartitionPrice.profile model.rat W s (s+2) (8*a.C) ∧
    (GeneralPaperUnsignedCellPartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (8*a.C) opposite signedSummary options).2≤
      GeneralPaperUnsignedCellPartitionPrice.arithmeticProfile s (s+2) ∧
    (GeneralPaperSignedCellPartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (8*a.C) own options).2≤
      GeneralPaperSignedCellPartitionPrice.arithmeticProfile s (s+2) := by
  have h := GeneralPaperActualOccurrencePreparation.four_codes bits index price W m k Qv a c hc digits trees hValid hPaths arrays hArrays
  have hOwn : ∀ r,((if response then arrays.q else arrays.p).read j).read r<8*a.C := by
    cases response
    · exact h.1 j
    · exact h.2.1 j
  have hOther : ∀ r,((if response then arrays.p else arrays.q).read j).read r<8*a.C := by
    cases response
    · exact h.2.1 j
    · exact h.1 j
  have hSigned : ∀ r,((signed response arrays).read j).read r<2*(8*a.C) := by
    cases response
    · exact h.2.2.1 j
    · exact h.2.2.2 j
  have hOptions := option_codes a response arrays ready hReady j
  exact ⟨GeneralPaperUnsignedCellPartitionPrice.bit_work model.rat model.monotone W (8*a.C) _ _ _ hOther hSigned hOptions,
    GeneralPaperSignedCellPartitionPrice.bit_work model.rat model.monotone W (8*a.C) _ _ hOwn hOptions,
    GeneralPaperUnsignedCellPartitionPrice.arithmetic_work (8*a.C) _ _ _ hOther hSigned hOptions,
    GeneralPaperSignedCellPartitionPrice.arithmetic_work (8*a.C) _ _ hOwn hOptions⟩

theorem cell_counts {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (a : Alphabet) (response : Bool)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k) (ready : GeneralPaperCatalogueOptimizer.Ready m k) (j : Fin m) :
    let own := (if response then arrays.q else arrays.p).read j
    let opposite := (if response then arrays.p else arrays.q).read j
    let signedSummary := (signed response arrays).read j
    let options := ready.data.codes.read j
    let s := (GeneralPaperSourceParameters.prepare k).summarySize
    (GeneralPaperUnsignedCellPartitionPrice.run bits index price W (8*a.C) opposite signedSummary options).1.count≤4*s+3 ∧
    (GeneralPaperSignedCellPartitionPrice.run bits index price W (8*a.C) own options).1.count≤6*s+6 := by
  have hu := GeneralPaperUnsignedCellPartitionPrice.count_bound bits index price W (8*a.C)
    ((if response then arrays.p else arrays.q).read j) ((signed response arrays).read j) (ready.data.codes.read j)
  have hs := GeneralPaperSignedCellPartitionPrice.count_bound bits index price W (8*a.C)
    ((if response then arrays.q else arrays.p).read j) (ready.data.codes.read j)
  exact ⟨hu.trans_eq (by omega),hs.trans_eq (by omega)⟩

theorem representative_prices {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k) (ready : GeneralPaperCatalogueOptimizer.Ready m k) (j : Fin m) :
    let own := (if response then arrays.q else arrays.p).read j
    let opposite := (if response then arrays.p else arrays.q).read j
    let signedSummary := (signed response arrays).read j
    let options := ready.data.codes.read j
    let s := (GeneralPaperSourceParameters.prepare k).summarySize
    let ub := GeneralPaperUnsignedCellPartitionPrice.run true (fun w => w) model.rat W (8*a.C) opposite signedSummary options
    let sb := GeneralPaperSignedCellPartitionPrice.run true (fun w => w) model.rat W (8*a.C) own options
    let ua := GeneralPaperUnsignedCellPartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (8*a.C) opposite signedSummary options
    let sa := GeneralPaperSignedCellPartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (8*a.C) own options
    (GeneralPaperCellRepresentativePrice.run true (fun w => w) model.rat W ub.1.intervals).2≤
      GeneralPaperCellRepresentativePrice.profile model.rat W (4*s+3) ∧
    (GeneralPaperCellRepresentativePrice.run true (fun w => w) model.rat W sb.1.intervals).2≤
      GeneralPaperCellRepresentativePrice.profile model.rat W (6*s+6) ∧
    (GeneralPaperCellRepresentativePrice.run false (fun _ => 1) (fun _ => 1) 1 ua.1.intervals).2≤
      GeneralPaperCellRepresentativePrice.arithmeticProfile (4*s+3) ∧
    (GeneralPaperCellRepresentativePrice.run false (fun _ => 1) (fun _ => 1) 1 sa.1.intervals).2≤
      GeneralPaperCellRepresentativePrice.arithmeticProfile (6*s+6) := by
  have hb := cell_counts true (fun w => w) model.rat W a response arrays ready j
  have ha := cell_counts false (fun _ => 1) (fun _ => 1) 1 a response arrays ready j
  exact ⟨(GeneralPaperCellRepresentativePrice.bit_work model.rat model.monotone W _).trans
      (GeneralPaperCellRepresentativePrice.profile_mono model.rat model.monotone W _ _ hb.1),
    (GeneralPaperCellRepresentativePrice.bit_work model.rat model.monotone W _).trans
      (GeneralPaperCellRepresentativePrice.profile_mono model.rat model.monotone W _ _ hb.2),
    (GeneralPaperCellRepresentativePrice.arithmetic_work _).trans (GeneralPaperCellRepresentativePrice.arithmetic_profile_mono _ _ ha.1),
    (GeneralPaperCellRepresentativePrice.arithmetic_work _).trans (GeneralPaperCellRepresentativePrice.arithmetic_profile_mono _ _ ha.2)⟩


theorem epoch_cache_partitions_data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (a : Alphabet) (response : Bool) (arrays : GeneralPaperFourSummaryArrays.Arrays m k) (j : Fin m) :
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    let ready := if response then cache.response else cache.candidate
    let own := (if response then arrays.q else arrays.p).read j
    let opposite := (if response then arrays.p else arrays.q).read j
    let signedSummary := (signed response arrays).read j
    let options := ready.data.codes.read j
    (GeneralPaperUnsignedCellPartitionPrice.run bits index price W (8*a.C) opposite signedSummary options).1=
      (if response then (cache.plans.read j).qCells.partition else (cache.plans.read j).pCells.partition) ∧
    (GeneralPaperSignedCellPartitionPrice.run bits index price W (8*a.C) own options).1=
      (if response then (cache.plans.read j).muCells.partition else (cache.plans.read j).lambdaCells.partition) := by
  dsimp only
  rw [GeneralPaperUnsignedCellPartitionPrice.data,GeneralPaperSignedCellPartitionPrice.data]
  cases response <;>
    simp only [signed,Bool.false_eq_true,ite_false,ite_true,GeneralPaperCatalogueEpochCache.plan_read] <;>
    constructor <;> rfl

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (response : Bool) (j : Fin m) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    let ready := if response then cache.response else cache.candidate
    let own := (if response then arrays.q else arrays.p).read j
    let opposite := (if response then arrays.p else arrays.q).read j
    let signedSummary := (signed response arrays).read j
    let options := ready.data.codes.read j
    let s := (GeneralPaperSourceParameters.prepare k).summarySize
    (GeneralPaperUnsignedCellPartitionPrice.run true (fun w => w) model.rat W (8*a.C) opposite signedSummary options).2≤
      GeneralPaperUnsignedCellPartitionPrice.profile model.rat W s (s+2) (8*a.C) ∧
    (GeneralPaperSignedCellPartitionPrice.run true (fun w => w) model.rat W (8*a.C) own options).2≤
      GeneralPaperSignedCellPartitionPrice.profile model.rat W s (s+2) (8*a.C) ∧
    (GeneralPaperUnsignedCellPartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (8*a.C) opposite signedSummary options).2≤
      GeneralPaperUnsignedCellPartitionPrice.arithmeticProfile s (s+2) ∧
    (GeneralPaperSignedCellPartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (8*a.C) own options).2≤
      GeneralPaperSignedCellPartitionPrice.arithmeticProfile s (s+2) :=
  generated_work true (fun w => w) model.rat W m k Qv a c hc _ _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) _ rfl model response _
    (by cases response <;> rfl) j

end Blotto.GeneralPaperActualCellPartitions
