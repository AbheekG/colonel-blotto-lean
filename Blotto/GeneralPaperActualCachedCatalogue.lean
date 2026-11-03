import Blotto.GeneralPaperCachedCataloguePrice

/-! Generated signed summaries and retained epoch forests supply all
complete cached-catalogue premises, in both cost models and both modes.
-/
namespace Blotto.GeneralPaperActualCachedCatalogue
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOptionPlans (signed)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem generated_work (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel)
    (W m k Qv : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hArrays : arrays=(GeneralPaperFourSummaryArrays.run bits index price W m k Qv a c hc digits trees).1)
    (response : Bool) (field : Fin m) :
    let summary := (signed response arrays).read field
    (GeneralPaperCachedCatalogueExecution.run true (fun w => w) model W a response summary).2≤
      GeneralPaperCachedCataloguePrice.profile model W (GeneralPaperSourceParameters.prepare k).summarySize a ∧
    (GeneralPaperCachedCatalogueExecution.run false (fun _ => 1) model 1 a response summary).2≤
      GeneralPaperCachedCataloguePrice.arithmeticProfile (GeneralPaperSourceParameters.prepare k).summarySize a := by
  have hCodes := GeneralPaperActualCataloguePartition.generated_codes bits index price W m k Qv a c hc digits trees
    hValid hPaths arrays hArrays response field
  exact ⟨GeneralPaperCachedCataloguePrice.bit_work model W a response _ hCodes,
    GeneralPaperCachedCataloguePrice.arithmetic_work model a response _ hCodes⟩

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (response : Bool) (field : Fin m) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let summary := (signed response arrays).read field
    (GeneralPaperCachedCatalogueExecution.run true (fun w => w) model W a response summary).2≤
      GeneralPaperCachedCataloguePrice.profile model W (GeneralPaperSourceParameters.prepare k).summarySize a ∧
    (GeneralPaperCachedCatalogueExecution.run false (fun _ => 1) model 1 a response summary).2≤
      GeneralPaperCachedCataloguePrice.arithmeticProfile (GeneralPaperSourceParameters.prepare k).summarySize a :=
  generated_work true (fun w => w) model.rat model W m k Qv a c hc _ _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) _ rfl response field

end Blotto.GeneralPaperActualCachedCatalogue
