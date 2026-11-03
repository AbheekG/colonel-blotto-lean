import Blotto.GeneralPaperEpochCachePreparation

/-! Full tree-to-epoch preparation: four summary-family loops, both optimizer
preparations and all eight field plans. The caller supplies retained prepared
powers/mesh; actual valid epoch trees derive every code premise. No source,
parameter, encoding or calibration replay is introduced.
-/
namespace Blotto.GeneralPaperTreeEpochPreparation
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) : GeneralPaperCatalogueEpochCache.Cache m k × ℕ :=
  let arrays := GeneralPaperFourSummaryArrays.run bits index (primitive bits model) W m k Qv a c hc digits trees
  let prepared := GeneralPaperEpochCachePreparation.run bits index model W k c.controls.source.meshDenominator a arrays.1
    (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc)
  (prepared.1,arrays.2+prepared.2+128*W)

def profile (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperFourSummaryArrays.profile model.rat W m a.lambda k Qv+
    GeneralPaperEpochCachePreparation.profile model W m k a+128*W

def arithmeticProfile (m k Qv : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperFourSummaryArrays.arithmeticProfile m a.lambda k Qv+
    GeneralPaperEpochCachePreparation.arithmeticProfile m k a+128

theorem data (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees) :
    (run bits index model W m k Qv a c hc digits trees).1=
      GeneralPaperCatalogueTreeCache.prepare c.powers digits a k trees := by
  unfold run
  dsimp only
  rw [GeneralPaperEpochCachePreparation.data]
  exact GeneralPaperFourSummaryArrays.epoch_cache_data bits index (primitive bits model) W m k Qv a c hc digits trees hValid hPaths

theorem bit_work (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (hDigits : digits=GeneralPaperQuantileComparison.width a.lambda k)
    (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees) :
    (run true (fun w => w) model W m k Qv a c hc digits trees).2≤profile model W m k Qv a := by
  let arrays := GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc digits trees
  have hCodes := GeneralPaperActualOccurrencePreparation.four_codes true (fun w => w) model.rat W m k Qv a c hc digits trees
    hValid hPaths arrays.1 rfl
  have hs := GeneralPaperFourSummaryArrays.bit_work model.rat model.monotone W m k Qv a c hc digits hDigits trees hValid hPaths
  have he := GeneralPaperEpochCachePreparation.bit_work model W k c.controls.source.meshDenominator a arrays.1
    (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc) hCodes.1 hCodes.2.1 hCodes.2.2.1 hCodes.2.2.2
  exact Nat.add_le_add_right (Nat.add_le_add hs he) _

theorem arithmetic_work (model : RationalCostModel) (m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (hDigits : digits=GeneralPaperQuantileComparison.width a.lambda k)
    (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees) :
    (run false (fun _ => 1) model 1 m k Qv a c hc digits trees).2≤arithmeticProfile m k Qv a := by
  let arrays := GeneralPaperFourSummaryArrays.run false (fun _ => 1) (fun _ => 1) 1 m k Qv a c hc digits trees
  have hCodes := GeneralPaperActualOccurrencePreparation.four_codes false (fun _ => 1) (fun _ => 1) 1 m k Qv a c hc digits trees
    hValid hPaths arrays.1 rfl
  have hs := GeneralPaperFourSummaryArrays.arithmetic_work m k Qv a c hc digits hDigits trees
  have he := GeneralPaperEpochCachePreparation.arithmetic_work model k c.controls.source.meshDenominator a arrays.1
    (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc) hCodes.1 hCodes.2.1 hCodes.2.2.1 hCodes.2.2.2
  exact Nat.add_le_add_right (Nat.add_le_add hs he) _

theorem same_data (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees) :
    (run true (fun w => w) model W m k Qv a c hc digits trees).1=
      (run false (fun _ => 1) model 1 m k Qv a c hc digits trees).1 := by
  rw [data true (fun w => w) model W m k Qv a c hc digits trees hValid hPaths,
    data false (fun _ => 1) model 1 m k Qv a c hc digits trees hValid hPaths]

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    (run true (fun w => w) model W m k Qv a c hc (GeneralPaperQuantileComparison.width a.lambda k) trees).2≤profile model W m k Qv a ∧
    (run false (fun _ => 1) model 1 m k Qv a c hc (GeneralPaperQuantileComparison.width a.lambda k) trees).2≤arithmeticProfile m k Qv a := by
  have hv := GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he
  have hp := GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he
  exact ⟨bit_work model W m k Qv a c hc _ rfl _ hv hp,arithmetic_work model m k Qv a c hc _ rfl _ hv hp⟩

theorem epoch_data {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    (run bits index model W m k Qv a c hc (GeneralPaperQuantileComparison.width a.lambda k) trees).1=
      GeneralPaperCatalogueTreeCache.prepare c.powers (GeneralPaperQuantileComparison.width a.lambda k) a k trees :=
  data bits index model W m k Qv a c hc _ _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he)

end Blotto.GeneralPaperTreeEpochPreparation
