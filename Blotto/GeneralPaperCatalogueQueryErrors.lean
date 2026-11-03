import Blotto.GeneralPaperCatalogueTreeCDF

/-! Actual rounded CDF and separately rounded interval queries inherit the
5*nu+theta and 10*nu+theta errors from the concrete native snapshot. These
interfaces retain arbitrary incoming mass; the preceding tree theorem
supplies the initial probability and CDF certificate from sparse nodes.
-/
namespace Blotto.GeneralPaperCatalogueQueryErrors
open scoped BigOperators
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueEpochMetadata GeneralPaperCatalogueEpochCDF
open GeneralPaperCDFReweighting
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

theorem block_coherent {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (count : ℕ) (j : Fin m) :
    (block learner (snapshotAt run count j)).Coherent := by
  have he := snapshot_coherent run count j
  cases learner with
  | p => exact he.1
  | q => exact he.2.1
  | lambda => exact he.2.2.1
  | mu => exact he.2.2.2

theorem block_positive {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    (block learner (snapshotAt (selected cache Qv weights Bc Br) count j)).Positive := by
  have he := selected_positive cache Qv weights Bc Br count hCount j
  cases learner with
  | p => exact he.1
  | q => exact he.2.1
  | lambda => exact he.2.2.1
  | mu => exact he.2.2.2

theorem cdf_error {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (j : Fin m) (incoming : ℕ → ℝ)
    (hIncoming : ProbabilityOn incoming (width learner cache-1))
    (hClose : GeneralPaperCDFReweighting.CDFClose incoming (GeneralPaperSummaryOccurrences.uniform (summary learner cache j).read)
      (width learner cache-1) ((GeneralPaperSourceParameters.prepare k).nu:ℝ))
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (cut : ℕ) (hCut : cut≤width learner cache) :
    |currentCDF learner cache Qv weights Bc Br incoming count j cut-
      (GeneralPaperRankedCDFQuery.referenceValue k (summary learner cache j)
        (block learner (snapshotAt (selected cache Qv weights Bc Br) count j)).cdf cut:ℝ)|≤
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  let b := block learner (snapshotAt (selected cache Qv weights Bc Br) count j)
  let rank := (GeneralPaperSelectedRank.lookup k (summary learner cache j) cut).position
  have hc : b.cdf=GeneralPaperEpochPrefixArray.build b.values := block_coherent learner _ count j
  have hp : 0<∑ r, b.values.read r := block_positive learner cache Qv weights Bc Br count hCount j
  have ht : 0<b.cdf.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize) := by
    rw [hc,GeneralPaperEpochPrefixQuery.read_total]
    exact hp
  have hn : b.cdf.read rank≤b.cdf.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize) := by
    rw [hc]
    exact GeneralPaperEpochPrefixQuery.read_le_total b.values rank
  have hr := GeneralPaperCatalogueEpochCDF.raw_error learner cache Qv weights Bc Br hOrdered hCodes j incoming hIncoming hClose count hCount cut hCut
  exact GeneralPaperCDFMesh.selected_true_error k (b.cdf.read rank)
    (b.cdf.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize)) ht hn _ _ hr.le

theorem interval_error {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (j : Fin m) (incoming : ℕ → ℝ)
    (hIncoming : ProbabilityOn incoming (width learner cache-1))
    (hClose : GeneralPaperCDFReweighting.CDFClose incoming (GeneralPaperSummaryOccurrences.uniform (summary learner cache j).read)
      (width learner cache-1) ((GeneralPaperSourceParameters.prepare k).nu:ℝ))
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (lo hi : ℕ) (hOrder : lo≤hi) (hHi : hi≤width learner cache) :
    |(currentCDF learner cache Qv weights Bc Br incoming count j hi-currentCDF learner cache Qv weights Bc Br incoming count j lo)-
      (GeneralPaperRankedInterval.referenceValue k (summary learner cache j)
        (block learner (snapshotAt (selected cache Qv weights Bc Br) count j)).cdf lo hi:ℝ)|≤
      10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  let b := block learner (snapshotAt (selected cache Qv weights Bc Br) count j)
  have hc : b.cdf=GeneralPaperEpochPrefixArray.build b.values := block_coherent learner _ count j
  have hp : 0<∑ r, b.values.read r := block_positive learner cache Qv weights Bc Br count hCount j
  have hl := GeneralPaperCatalogueEpochCDF.raw_error learner cache Qv weights Bc Br hOrdered hCodes j incoming hIncoming hClose count hCount lo (hOrder.trans hHi)
  have hh := GeneralPaperCatalogueEpochCDF.raw_error learner cache Qv weights Bc Br hOrdered hCodes j incoming hIncoming hClose count hCount hi hHi
  change |_-GeneralPaperRawEpochCDF.raw k (summary learner cache j) b.cdf lo|<_ at hl
  change |_-GeneralPaperRawEpochCDF.raw k (summary learner cache j) b.cdf hi|<_ at hh
  rw [hc] at hl hh ⊢
  have he := GeneralPaperIntervalError.from_prefix_errors k b.values
    (GeneralPaperSelectedRank.lookup k (summary learner cache j) lo).position
    (GeneralPaperSelectedRank.lookup k (summary learner cache j) hi).position
    (GeneralPaperSelectedRank.lookup_monotone k _ (hOrdered learner j) hOrder) hp _ _
    (5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)) hl.le hh.le
  unfold GeneralPaperRankedInterval.referenceValue GeneralPaperRankedInterval.referenceCount
  convert he using 1 <;> ring

noncomputable def signedTail {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (incoming : ℕ → ℝ) (count : ℕ) (j : Fin m) (U a : ℕ) : ℝ :=
  (currentCDF learner cache Qv weights Bc Br incoming count j U-currentCDF learner cache Qv weights Bc Br incoming count j a)-
    (currentCDF learner cache Qv weights Bc Br incoming count j (2*U)-currentCDF learner cache Qv weights Bc Br incoming count j (U+a))

theorem signed_tail_error {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (j : Fin m) (incoming : ℕ → ℝ)
    (hIncoming : ProbabilityOn incoming (width learner cache-1))
    (hClose : GeneralPaperCDFReweighting.CDFClose incoming (GeneralPaperSummaryOccurrences.uniform (summary learner cache j).read)
      (width learner cache-1) ((GeneralPaperSourceParameters.prepare k).nu:ℝ))
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (U a : ℕ) (hWidth : width learner cache=2*U) (hA : a≤U) :
    |signedTail learner cache Qv weights Bc Br incoming count j U a-
      (GeneralPaperSignedTailProperties.signedValue k U (summary learner cache j)
        (block learner (snapshotAt (selected cache Qv weights Bc Br) count j)).cdf a:ℝ)|≤
      20*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+2*((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  have hp := interval_error learner cache Qv weights Bc Br hOrdered hCodes j incoming hIncoming hClose count hCount a U hA (by omega)
  have hn := interval_error learner cache Qv weights Bc Br hOrdered hCodes j incoming hIncoming hClose count hCount (U+a) (2*U) (by omega) (by omega)
  have he := GeneralPaperEpochCDF.interval_error _ _ _ _
    (10*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ)) hp hn
  unfold signedTail GeneralPaperSignedTailProperties.signedValue GeneralPaperSignedTailProperties.tailValue
  simp only [Nat.zero_add,two_mul,Rat.cast_sub] at he ⊢
  convert he using 1 <;> (first | rfl | ring)

end Blotto.GeneralPaperCatalogueQueryErrors
