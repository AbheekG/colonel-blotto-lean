import Blotto.GeneralPaperEncodedEpochCache

/-! Actual reached forests and one-time preparation returns supply the full
epoch-cache storage bound. Native/priced cache equality reuses existing
results and performs no source, plan or catalogue reconstruction. -/
namespace Blotto.GeneralPaperActualEpochCacheStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem epoch {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    let shared := prepare a k Qv weights Bc Br
    let cache := GeneralPaperCatalogueShared.cache shared a k (treesAt shared a k count)
    GeneralPaperEncodedEpochCache.footprint W cache≤GeneralPaperEncodedEpochCache.profile W m a.lambda k :=
  GeneralPaperEncodedEpochCache.bounded W _ (GeneralPaperCatalogueOuterValidity.cache_codes a k Qv weights Bc Br count)

theorem priced {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k count
    GeneralPaperEncodedEpochCache.footprint W
      (GeneralPaperTreeEpochPreparation.run bits index model W m k Qv a c hc shared.wordWidth trees).1≤
        GeneralPaperEncodedEpochCache.profile W m a.lambda k := by
  have hd := GeneralPaperTreeEpochPreparation.epoch_data bits index model W k Qv a c hc weights Bc Br count he
  have hp : c.powers=(prepare a k Qv weights Bc Br).powers := by rw [hc]; rfl
  rw [hp] at hd
  dsimp only
  erw [hd]
  exact epoch W k Qv a weights Bc Br count

theorem prepared_epoch {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let cache := GeneralPaperCatalogueShared.cache shared a k (treesAt shared a k count)
    GeneralPaperEncodedEpochCache.footprint W cache≤GeneralPaperEncodedEpochCache.profile W m a.lambda k := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br count

end Blotto.GeneralPaperActualEpochCacheStorage
