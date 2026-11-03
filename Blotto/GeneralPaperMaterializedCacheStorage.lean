import Blotto.GeneralPaperCeilingConstructionStorage
import Blotto.GeneralPaperEncodedSharedSource

/-! Retained parameter/power/grid caches contain more than native Shared.
Every returned record is counted literally, even when this conservatively
counts Shared-borrowed data again. These joins reuse actual preparation
returns and preserve explicit weight and rational-budget encodings. -/
namespace Blotto.GeneralPaperMaterializedCacheStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def powerFootprint (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) : ℕ :=
  GeneralPaperPreparationCacheStorage.footprint W c.controls+GeneralPaperEncodedPreparedPowers.footprint W c.powers+64*W

def powerProfile (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperPreparationCacheStorage.profile W m lambda k Qv+GeneralPaperEncodedPreparedPowers.profile W m lambda k Qv+64*W

theorem power_native (W m lambda k Qv : ℕ) :
    powerFootprint W (GeneralPaperMaterializedPowerCache.specification m lambda k Qv)≤powerProfile W m lambda k Qv :=
  Nat.add_le_add_right (Nat.add_le_add (GeneralPaperPreparationCacheStorage.native W m lambda k Qv)
    (GeneralPaperEncodedPreparedPowers.native W m lambda k Qv)) _

def gridFootprint (W : ℕ) (c : GeneralPaperMaterializedGridCache.Cache) : ℕ :=
  powerFootprint W c.source+GeneralPaperEncodedSharedParameters.preparedProfitFootprint W c.profit+64*W

def gridProfile (W m lambda k Qv : ℕ) : ℕ :=
  powerProfile W m lambda k Qv+GeneralPaperEncodedSharedParameters.preparedProfitProfile W m lambda k Qv+64*W

theorem grid_native (W m lambda k Qv : ℕ) :
    gridFootprint W (GeneralPaperMaterializedGridCache.specification m lambda k Qv)≤gridProfile W m lambda k Qv :=
  Nat.add_le_add_right (Nat.add_le_add (power_native W m lambda k Qv)
    (GeneralPaperEncodedSharedParameters.prepared_profit W m lambda k Qv)) _

theorem power_returned (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) :
    powerFootprint W (GeneralPaperMaterializedPowerCache.prepare primitive W m lambda k Qv).1≤powerProfile W m lambda k Qv := by
  rw [GeneralPaperMaterializedPowerCache.data]
  exact power_native W m lambda k Qv

theorem grid_returned (index primitive : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) :
    gridFootprint W (GeneralPaperMaterializedGridCache.extend index primitive W c).1≤gridProfile W m lambda k Qv := by
  rw [GeneralPaperMaterializedGridCache.data index primitive W m lambda k Qv c hc]
  exact grid_native W m lambda k Qv

theorem shared {m : ℕ} (primitive : ℕ → ℕ) (W k Qv : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet)
    (c : GeneralPaperMaterializedGridCache.Cache) (hc : c=GeneralPaperMaterializedGridCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    gridFootprint W c+
      GeneralPaperEncodedSharedSource.footprint W (GeneralPaperCachedSharedPreparation.fromCache primitive W k a c weights Bc Br).1≤
      gridProfile W m a.lambda k Qv+GeneralPaperEncodedSharedSource.profile W k Qv a weights Bc Br := by
  rw [GeneralPaperCachedSharedPreparation.data primitive W k Qv a c hc weights Bc Br,hc]
  exact Nat.add_le_add (grid_native W m a.lambda k Qv) (GeneralPaperEncodedSharedSource.native W k Qv a weights Bc Br)

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    let result := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    gridFootprint W result.2+GeneralPaperEncodedSharedSource.footprint W result.1.2≤
      gridProfile W m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv+
        GeneralPaperEncodedSharedSource.profile W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact Nat.add_le_add (grid_native W m _ k Qv)
    (GeneralPaperEncodedSharedSource.native W k Qv _ weights Bc Br)

theorem prepared_arithmetic {m : ℕ} (W k Qv : ℕ) (b : ℝ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    let result := (GeneralPaperPreparedSharedSource.arithmetic k Qv b weights Bc Br).1
    gridFootprint W result.2+GeneralPaperEncodedSharedSource.footprint W result.1.2≤
      gridProfile W m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv+
        GeneralPaperEncodedSharedSource.profile W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.arithmetic_data]
  exact Nat.add_le_add (grid_native W m _ k Qv)
    (GeneralPaperEncodedSharedSource.native W k Qv _ weights Bc Br)

end Blotto.GeneralPaperMaterializedCacheStorage
