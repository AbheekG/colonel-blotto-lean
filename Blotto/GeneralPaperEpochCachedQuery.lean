import Blotto.GeneralPaperEpochPrefixQuery

/-! Actual local-level arrays, stored power numerators, native prefix arrays
and the bounded mesh quotient form one numerical CDF-query contract. The
cached rank/location interface and the local loss callbacks remain explicit;
no total positivity or supplied local-level history is needed.
-/
namespace Blotto.GeneralPaperEpochCachedQuery
open scoped BigOperators
open GeneralPaperPreparedPowers GeneralPaperGeometricLevels GeneralPaperGeometricVariation
open GeneralPaperOrderedVariation GeneralPaperEpochPowerQueries
set_option autoImplicit false
set_option maxHeartbeats 3500000

def numerators {s : ℕ} (prepared : Prepared) (delta : ℕ → FixedArrayTable s ℕ) (count : ℕ) : FixedArrayTable s ℕ :=
  buildNumerators prepared (GeneralPaperEpochLevelArray.execute delta count).1

def prefixes {s : ℕ} (prepared : Prepared) (delta : ℕ → FixedArrayTable s ℕ) (count : ℕ) : FixedArrayTable (s+1) ℕ :=
  GeneralPaperEpochPrefixArray.build (numerators prepared delta count)

theorem total_positive {n s : ℕ} (hn : 0<n) (hs : 0<s) (lambda k start count : ℕ)
    (increment : ℕ → Fin n → ℕ) (location : Fin s → Fin n) (delta : ℕ → FixedArrayTable s ℕ)
    (hDelta : ∀ t<count, ∀ r, (delta t).read r=increment (start+t) (location r))
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2) :
    0<∑ r, (numerators (prepare lambda k) delta count).read r := by
  let localLevels := (GeneralPaperEpochLevelArray.execute delta count).1
  have hLevels (r : Fin s) : localLevels.read r=levels (fun t => increment (start+t)) count (location r) :=
    GeneralPaperEpochLevelArray.cached_read delta increment location start count hDelta r
  have hBound (r : Fin s) : localLevels.read r≤GeneralPaperPowerPrecision.levelBound lambda k := by
    rw [hLevels]
    exact epoch_level_bound hn lambda k start count increment hCount hIncrement (location r)
  have hNormal := fun r => (query_certificate lambda k _ (hBound r)).2.1
  have hRange (r : Fin s) : (1/2:ℚ)≤GeneralPaperDyadicFloat.value (query (prepare lambda k) (localLevels.read r)).number ∧
      GeneralPaperDyadicFloat.value (query (prepare lambda k) (localLevels.read r)).number≤1 := by
    rw [hLevels]
    exact epoch_power_range hn lambda k start count increment hCount hIncrement hMagnitude (location r)
  exact materialized_total_positive hs (prepare lambda k) localLevels (GeneralPaperPowerPrecision.unit_power lambda k)
    hNormal (fun r => (hRange r).1) (fun r => (hRange r).2)

theorem rounded_cdf_error {n s : ℕ} (hn : 0<n) (hs : 0<s) (lambda k start count : ℕ)
    (increment : ℕ → Fin n → ℕ) (location : Fin s → Fin n) (delta : ℕ → FixedArrayTable s ℕ)
    (hDelta : ∀ t<count, ∀ r, (delta t).read r=increment (start+t) (location r))
    (hClose : GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta) increment start (code hn i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location r).val)) (n-1)
      ((GeneralPaperSourceParameters.prepare k).nu:ℝ))
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code hn i)):ℝ)) (n-1)≤4)
    (cut : ℕ) (hCut : cut≤n) (rank : Fin (s+1))
    (hRank : ∀ r, (location r).val<cut ↔ r.val<rank.val) :
    |prefixMass (fun i => probability (geometricBase (GeneralPaperSourceParameters.prepare k).eta
      (GeneralPaperSourceParameters.prepare k).theta) increment (start+count) (code hn i)) cut-
      (GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
        (GeneralPaperEpochPrefixQuery.query k (prefixes (prepare lambda k) delta count) rank).quotient:ℝ)|≤
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  let values := numerators (prepare lambda k) delta count
  let localLevels := (GeneralPaperEpochLevelArray.execute delta count).1
  have hLevels (r : Fin s) : localLevels.read r=levels (fun t => increment (start+t)) count (location r) :=
    GeneralPaperEpochLevelArray.cached_read delta increment location start count hDelta r
  have he := integer_cdf_error hn hs lambda k start count increment location localLevels hLevels hClose
    hCount hIncrement hMagnitude hVariation cut hCut
  have hNum := GeneralPaperEpochPrefixQuery.read_location_count values (fun r => (location r).val) rank cut hRank
  have hTotal := GeneralPaperEpochPrefixQuery.read_total values
  have hp := total_positive hn hs lambda k start count increment location delta hDelta hCount hIncrement hMagnitude
  have hPos : 0<(GeneralPaperEpochPrefixArray.build values).read (Fin.last s) := by rw [hTotal]; exact hp
  have hNative : |prefixMass (fun i => probability (geometricBase (GeneralPaperSourceParameters.prepare k).eta
      (GeneralPaperSourceParameters.prepare k).theta) increment (start+count) (code hn i)) cut-
      ((GeneralPaperEpochPrefixArray.build values).read rank:ℝ)/
        ((GeneralPaperEpochPrefixArray.build values).read (Fin.last s):ℝ)|≤5*((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
    rw [hNum,hTotal]
    exact he.le
  exact GeneralPaperCDFMesh.selected_true_error k _ _ hPos (GeneralPaperEpochPrefixQuery.read_le_total values rank)
    _ _ hNative

end Blotto.GeneralPaperEpochCachedQuery
