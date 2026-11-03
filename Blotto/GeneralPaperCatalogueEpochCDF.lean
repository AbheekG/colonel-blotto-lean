import Blotto.GeneralPaperCatalogueTreeCache

/-! Actual native epoch CDF queries approximate reweighting of any incoming
full probability law. The epoch's own finite increments, occurrence arrays,
power queries and exact native prefix sums supply the complete local join.
This preserves incoming mass instead of restarting the learner uniformly.
-/
namespace Blotto.GeneralPaperCatalogueEpochCDF
open scoped BigOperators
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueEpochMetadata GeneralPaperCatalogueHorizon
open GeneralPaperGeometricLevels GeneralPaperGeometricVariation GeneralPaperOrderedVariation GeneralPaperCDFReweighting
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

noncomputable def power {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (j : Fin m) (i : ℕ) : ℝ :=
  (GeneralPaperCachedMassJoin.base k:ℝ)^levels
    (fun t => finiteIncrement learner cache Qv weights Bc Br t j) count (code (width_positive learner cache) i)

noncomputable def currentCDF {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (incoming : ℕ → ℝ) (count : ℕ) (j : Fin m) (cut : ℕ) : ℝ :=
  reweightedCDF incoming (power learner cache Qv weights Bc Br count j) (width learner cache-1) cut

theorem local_levels {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hCodes : CodesValid cache) (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (j : Fin m) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (occurrence learner (fieldAt (selected cache Qv weights Bc Br) count j)).read r=
      levels (fun t => finiteIncrement learner cache Qv weights Bc Br t j) count (location learner cache hCodes j r) := by
  rw [occurrence_array]
  have he := GeneralPaperEpochLevelArray.cached_read (fun t => occurrenceDelta learner (deltaAt (selected cache Qv weights Bc Br) t j))
    (fun t => finiteIncrement learner cache Qv weights Bc Br t j) (location learner cache hCodes j) 0 count
    (fun t ht r => by simpa only [Nat.zero_add] using occurrence_finite learner cache Qv weights Bc Br hCodes count hCount t ht j r) r
  simpa only [Nat.zero_add] using he

theorem occurrence_cap {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (j : Fin m) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (occurrence learner (fieldAt (selected cache Qv weights Bc Br) count j)).read r≤GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k := by
  have he := selected_cap cache Qv weights Bc Br count hCount j
  cases learner with
  | p => exact he.1 r
  | q => exact he.2.1 r
  | lambda => exact he.2.2.1 r
  | mu => exact he.2.2.2.1 r

theorem rounded_range {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hCodes : CodesValid cache) (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (j : Fin m) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (1/2:ℚ)≤GeneralPaperDyadicFloat.value (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k)
      ((occurrence learner (fieldAt (selected cache Qv weights Bc Br) count j)).read r)).number ∧
    GeneralPaperDyadicFloat.value (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k)
      ((occurrence learner (fieldAt (selected cache Qv weights Bc Br) count j)).read r)).number≤1 := by
  have he := GeneralPaperEpochPowerQueries.epoch_power_range (width_positive learner cache) cache.alphabet.lambda k 0 count
    (fun t => finiteIncrement learner cache Qv weights Bc Br t j) hCount
    (fun t i => finite_bound learner cache Qv weights Bc Br t j i)
    (fun t i => finite_magnitude learner cache Qv weights Bc Br t j i) (location learner cache hCodes j r)
  simp only [Nat.zero_add] at he
  rw [←local_levels learner cache Qv weights Bc Br hCodes count hCount j r] at he
  exact he

theorem raw_identity {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (count : ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) (cut : ℕ) :
    let run := selected cache Qv weights Bc Br
    let degrees := occurrence learner (fieldAt run count j)
    let rounded := fun r => (GeneralPaperDyadicFloat.value (GeneralPaperPreparedPowers.query
      (GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k) (degrees.read r)).number:ℝ)
    GeneralPaperRawEpochCDF.raw k (summary learner cache j) (block learner (snapshotAt run count j)).cdf cut=
      GeneralPaperSummaryOccurrences.occurrencePrefix (summary learner cache j).read rounded cut/(∑ r, rounded r) := by
  dsimp only
  let run := selected cache Qv weights Bc Br
  let degrees := occurrence learner (fieldAt run count j)
  let prepared := GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k
  let values := GeneralPaperEpochPowerQueries.buildNumerators prepared degrees
  have hNormal := fun r => (GeneralPaperPreparedPowers.query_certificate cache.alphabet.lambda k (degrees.read r)
    (occurrence_cap learner cache Qv weights Bc Br count hCount j r)).2.1
  have hRange := rounded_range learner cache Qv weights Bc Br hCodes count hCount j
  have hIdentity := GeneralPaperEpochPowerQueries.materialized_cdf_identity prepared degrees (summary learner cache j).read cut
    (GeneralPaperPowerPrecision.unit_power cache.alphabet.lambda k) hNormal (fun r => (hRange r).1) (fun r => (hRange r).2)
  let rank := (GeneralPaperSelectedRank.lookup k (summary learner cache j) cut).position
  have hRank : ∀ r, (summary learner cache j).read r<cut ↔ r.val<rank.val :=
    GeneralPaperSelectedRank.lookup_spec k (summary learner cache j) (hOrdered learner j) cut
  have hNum := GeneralPaperEpochPrefixQuery.read_location_count values (summary learner cache j).read rank cut hRank
  rw [snapshot_block]
  change GeneralPaperRawEpochCDF.raw k (summary learner cache j) (GeneralPaperEpochPrefixArray.build values) cut=_
  unfold GeneralPaperRawEpochCDF.raw
  rw [hNum,GeneralPaperEpochPrefixQuery.read_total]
  exact hIdentity.symm

theorem raw_error {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (j : Fin m) (incoming : ℕ → ℝ)
    (hIncoming : ProbabilityOn incoming (width learner cache-1))
    (hClose : GeneralPaperCDFReweighting.CDFClose incoming (GeneralPaperSummaryOccurrences.uniform (summary learner cache j).read)
      (width learner cache-1) ((GeneralPaperSourceParameters.prepare k).nu:ℝ))
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (cut : ℕ) (hCut : cut≤width learner cache) :
    |currentCDF learner cache Qv weights Bc Br incoming count j cut-
      GeneralPaperRawEpochCDF.raw k (summary learner cache j) (block learner (snapshotAt (selected cache Qv weights Bc Br) count j)).cdf cut|<
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  have hs : 0<(GeneralPaperSourceParameters.prepare k).summarySize := by
    rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
    positivity
  let run := selected cache Qv weights Bc Br
  let degrees := occurrence learner (fieldAt run count j)
  let F := power learner cache Qv weights Bc Br count j
  let rounded := fun r => (GeneralPaperDyadicFloat.value (GeneralPaperPreparedPowers.query
    (GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k) (degrees.read r)).number:ℝ)
  have hLocation : ∀ r, (summary learner cache j).read r≤width learner cache-1 := by
    intro r
    have he := hCodes learner j r
    omega
  have hUniform := GeneralPaperSummaryOccurrences.uniform_probability hs (summary learner cache j).read _ hLocation
  have hSummary := GeneralPaperEpochCDF.epoch_cdf_close (width_positive learner cache) cache.alphabet.lambda k count
    (fun t => finiteIncrement learner cache Qv weights Bc Br t j) incoming
    (GeneralPaperSummaryOccurrences.uniform (summary learner cache j).read) ((GeneralPaperSourceParameters.prepare k).nu:ℝ)
    hIncoming hUniform hClose hCount (fun t i => finite_magnitude learner cache Qv weights Bc Br t j i)
    (fun t => finite_variation learner cache Qv weights Bc Br hOrdered hCodes t j) cut hCut
  change |currentCDF learner cache Qv weights Bc Br incoming count j cut-reweightedCDF _ F _ cut|≤_ at hSummary
  rw [GeneralPaperSummaryOccurrences.uniform_reweighted_cdf _ _ _ F hLocation] at hSummary
  have hLower : ∀ r, (1/2:ℝ)≤F ((summary learner cache j).read r) := by
    intro r
    change (1/2:ℝ)≤(GeneralPaperCachedMassJoin.base k:ℝ)^levels
      (fun t => finiteIncrement learner cache Qv weights Bc Br t j) count (code (width_positive learner cache) (location learner cache hCodes j r).val)
    rw [code_valid]
    have he := GeneralPaperEpochCDF.epoch_power_bounds (width_positive learner cache) cache.alphabet.lambda k count
      (fun t => finiteIncrement learner cache Qv weights Bc Br t j) hCount
      (fun t i => finite_magnitude learner cache Qv weights Bc Br t j i) (location learner cache hCodes j r)
    dsimp only [GeneralPaperCachedMassJoin.base]
    linarith only [he.1]
  have hRounded : ∀ r, 0≤rounded r := fun r =>
    (GeneralPaperPreparedPowers.query_positive cache.alphabet.lambda k _ (occurrence_cap learner cache Qv weights Bc Br count hCount j r)).le
  have hError : ∀ r, |F ((summary learner cache j).read r)-rounded r|≤((GeneralPaperSourceParameters.prepare k).nu:ℝ)/1024 := by
    intro r
    change |(GeneralPaperCachedMassJoin.base k:ℝ)^levels
      (fun t => finiteIncrement learner cache Qv weights Bc Br t j) count (code (width_positive learner cache) (location learner cache hCodes j r).val)-rounded r|≤_
    rw [code_valid,←local_levels learner cache Qv weights Bc Br hCodes count hCount j r]
    exact GeneralPaperPreparedPowers.query_error cache.alphabet.lambda k _ (occurrence_cap learner cache Qv weights Bc Br count hCount j r)
  have hf := GeneralPaperSummaryOccurrences.fresh_power_cdf_error (summary learner cache j).read _ hLocation
    (fun r => F ((summary learner cache j).read r)) rounded (((GeneralPaperSourceParameters.prepare k).nu:ℝ)/1024) hLower hRounded hError hs cut
  have hNu : (0:ℝ)<(GeneralPaperSourceParameters.prepare k).nu := by exact_mod_cast (GeneralPaperSourceParameters.positive k).2.2.1
  have hfStrict : |GeneralPaperSummaryOccurrences.occurrencePrefix (summary learner cache j).read
      (fun r => F ((summary learner cache j).read r)) cut/(∑ r, F ((summary learner cache j).read r))-
      GeneralPaperSummaryOccurrences.occurrencePrefix (summary learner cache j).read rounded cut/(∑ r, rounded r)|<
        ((GeneralPaperSourceParameters.prepare k).nu:ℝ)/128 := by linarith only [hf,hNu]
  rw [raw_identity learner cache Qv weights Bc Br hOrdered hCodes count hCount j cut]
  exact GeneralPaperEpochCDF.fresh_query_error _ _ _ _ hNu hSummary hfStrict

end Blotto.GeneralPaperCatalogueEpochCDF
