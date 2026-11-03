import Blotto.GeneralPaperIntervalError

/-! The actual local arrays and stored powers give the unrounded CDF
error below 5*nu. Two such endpoints and one interval rounding yield the
selected 10*nu+theta guarantee, with constructed ranks and a shared total.
-/
namespace Blotto.GeneralPaperRawEpochCDF
open scoped BigOperators
open GeneralPaperPreparedPowers GeneralPaperGeometricLevels GeneralPaperGeometricVariation GeneralPaperOrderedVariation
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def raw (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (cut : ℕ) : ℝ :=
  (preparedPrefix.read (GeneralPaperSelectedRank.lookup k summary cut).position:ℝ)/
    (preparedPrefix.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize):ℝ)

theorem error {n : ℕ} (hn : 0<n) (lambda k start count : ℕ) (increment : ℕ → Fin n → ℕ)
    (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (location : Fin (GeneralPaperSourceParameters.prepare k).summarySize → Fin n)
    (hLocation : ∀ r, (location r).val=summary.read r) (hMono : Monotone summary.read)
    (delta : ℕ → FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hDelta : ∀ t<count, ∀ r, (delta t).read r=increment (start+t) (location r))
    (hClose : GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (GeneralPaperCachedMassJoin.base k) increment start (code hn i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location r).val)) (n-1)
      ((GeneralPaperSourceParameters.prepare k).nu:ℝ))
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code hn i)):ℝ)) (n-1)≤4)
    (cut : ℕ) (hCut : cut≤n) :
    |prefixMass (fun i => probability (GeneralPaperCachedMassJoin.base k) increment (start+count) (code hn i)) cut-
      raw k summary (GeneralPaperEpochCachedQuery.prefixes (prepare lambda k) delta count) cut|<
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  have hs : 0<(GeneralPaperSourceParameters.prepare k).summarySize := by
    rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
    positivity
  let localLevels := (GeneralPaperEpochLevelArray.execute delta count).1
  let values := GeneralPaperEpochCachedQuery.numerators (prepare lambda k) delta count
  have hLevels (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
      localLevels.read r=levels (fun t => increment (start+t)) count (location r) :=
    GeneralPaperEpochLevelArray.cached_read delta increment location start count hDelta r
  have he := GeneralPaperEpochPowerQueries.integer_cdf_error hn hs lambda k start count increment location localLevels hLevels hClose
    hCount hIncrement hMagnitude hVariation cut hCut
  have hRank (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
      (location r).val<cut ↔ r.val<(GeneralPaperSelectedRank.lookup k summary cut).position.val := by
    rw [hLocation]
    exact GeneralPaperSelectedRank.lookup_spec k summary hMono cut r
  have hNum := GeneralPaperEpochPrefixQuery.read_location_count values (fun r => (location r).val)
    (GeneralPaperSelectedRank.lookup k summary cut).position cut hRank
  change |_-((GeneralPaperEpochPrefixArray.build values).read (GeneralPaperSelectedRank.lookup k summary cut).position:ℝ)/
    ((GeneralPaperEpochPrefixArray.build values).read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize):ℝ)|< _
  rw [hNum,GeneralPaperEpochPrefixQuery.read_total]
  exact he

theorem interval_error {n : ℕ} (hn : 0<n) (lambda k start count : ℕ) (increment : ℕ → Fin n → ℕ)
    (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (location : Fin (GeneralPaperSourceParameters.prepare k).summarySize → Fin n)
    (hLocation : ∀ r, (location r).val=summary.read r) (hMono : Monotone summary.read)
    (delta : ℕ → FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hDelta : ∀ t<count, ∀ r, (delta t).read r=increment (start+t) (location r))
    (hClose : GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (GeneralPaperCachedMassJoin.base k) increment start (code hn i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location r).val)) (n-1)
      ((GeneralPaperSourceParameters.prepare k).nu:ℝ))
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code hn i)):ℝ)) (n-1)≤4)
    (lo hi : ℕ) (hOrder : lo≤hi) (hHi : hi≤n) :
    |(prefixMass (fun i => probability (GeneralPaperCachedMassJoin.base k) increment (start+count) (code hn i)) hi-
        prefixMass (fun i => probability (GeneralPaperCachedMassJoin.base k) increment (start+count) (code hn i)) lo)-
      (GeneralPaperRankedInterval.referenceValue k summary (GeneralPaperEpochCachedQuery.prefixes (prepare lambda k) delta count) lo hi:ℝ)|≤
      10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  have hl := error hn lambda k start count increment summary location hLocation hMono delta hDelta hClose hCount hIncrement hMagnitude hVariation lo (hOrder.trans hHi)
  have hh := error hn lambda k start count increment summary location hLocation hMono delta hDelta hClose hCount hIncrement hMagnitude hVariation hi hHi
  have hs : 0<(GeneralPaperSourceParameters.prepare k).summarySize := by
    rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
    positivity
  have hp := GeneralPaperEpochCachedQuery.total_positive hn hs lambda k start count increment location delta hDelta hCount hIncrement hMagnitude
  have he := GeneralPaperIntervalError.from_prefix_errors k (GeneralPaperEpochCachedQuery.numerators (prepare lambda k) delta count)
    (GeneralPaperSelectedRank.lookup k summary lo).position (GeneralPaperSelectedRank.lookup k summary hi).position
    (GeneralPaperSelectedRank.lookup_monotone k summary hMono hOrder) hp _ _ (5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)) hl.le hh.le
  calc
    _ ≤ 2*(5*((GeneralPaperSourceParameters.prepare k).nu:ℝ))+((GeneralPaperSourceParameters.prepare k).theta:ℝ) := he
    _ = _ := by ring

end Blotto.GeneralPaperRawEpochCDF
