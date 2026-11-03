import Blotto.GeneralPaperCatalogueOptimizerPreparation

/-! Retained generated summaries supply all complete optimizer-preparation
premises. Both modes/models return the actual epoch-cache Ready object;
field-plan construction and full epoch preparation remain separate joins.
-/
namespace Blotto.GeneralPaperActualCataloguePreparation
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOptionPlans (signed)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem epoch_cache_ready_data {m k : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W mesh : ℕ)
    (a : Alphabet) (response : Bool) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (GeneralPaperCatalogueOptimizerPreparation.run bits index model W k mesh a response (signed response arrays) hMesh).1=
      if response then (GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu).response
      else (GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu).candidate := by
  rw [GeneralPaperCatalogueOptimizerPreparation.data]
  cases response <;> rfl

theorem generated_work (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel)
    (W m k Qv : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hArrays : arrays=(GeneralPaperFourSummaryArrays.run bits index price W m k Qv a c hc digits trees).1)
    (response : Bool) :
    let summary := signed response arrays
    (GeneralPaperCatalogueOptimizerPreparation.run true (fun w => w) model W k c.controls.source.meshDenominator a response summary
      (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc)).2≤
        GeneralPaperCatalogueOptimizerPreparation.profile model W m k a ∧
    (GeneralPaperCatalogueOptimizerPreparation.run false (fun _ => 1) model 1 k c.controls.source.meshDenominator a response summary
      (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc)).2≤
        GeneralPaperCatalogueOptimizerPreparation.arithmeticProfile m k a := by
  have hCodes : ∀ j r,((signed response arrays).read j).read r<2*(8*a.C) :=
    fun j => GeneralPaperActualCataloguePartition.generated_codes bits index price W m k Qv a c hc digits trees
      hValid hPaths arrays hArrays response j
  exact ⟨GeneralPaperCatalogueOptimizerPreparation.bit_work model W k c.controls.source.meshDenominator a response _
    (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc) hCodes,
    GeneralPaperCatalogueOptimizerPreparation.arithmetic_work model k c.controls.source.meshDenominator a response _
      (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc) hCodes⟩

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (response : Bool) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let summary := signed response arrays
    (GeneralPaperCatalogueOptimizerPreparation.run true (fun w => w) model W k c.controls.source.meshDenominator a response summary
      (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc)).2≤
        GeneralPaperCatalogueOptimizerPreparation.profile model W m k a ∧
    (GeneralPaperCatalogueOptimizerPreparation.run false (fun _ => 1) model 1 k c.controls.source.meshDenominator a response summary
      (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc)).2≤
        GeneralPaperCatalogueOptimizerPreparation.arithmeticProfile m k a :=
  generated_work true (fun w => w) model.rat model W m k Qv a c hc _ _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) _ rfl response

end Blotto.GeneralPaperActualCataloguePreparation
