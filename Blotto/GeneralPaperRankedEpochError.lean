import Blotto.GeneralPaperRankedCDFQuery

/-! Cached query ranks are constructed, not supplied. The ordered-summary
proof and actual rank cache close the remaining rank interface in the
local-array/power/prefix/mesh CDF-error theorem.
-/
namespace Blotto.GeneralPaperRankedEpochError
open GeneralPaperPreparedPowers GeneralPaperGeometricLevels GeneralPaperGeometricVariation GeneralPaperOrderedVariation
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem cached_error {n m : ℕ} (hn : 0<n) (lambda k start count : ℕ)
    (increment : ℕ → Fin n → ℕ)
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
    (cuts : FixedArrayTable m ℕ) (q : Fin m) (hCut : cuts.read q≤n) :
    |prefixMass (fun i => probability (GeneralPaperCachedMassJoin.base k) increment (start+count) (code hn i)) (cuts.read q)-
      (GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
        (GeneralPaperRankedCDFQuery.cached k (GeneralPaperEpochCachedQuery.prefixes (prepare lambda k) delta count)
          (GeneralPaperRankCache.build k summary cuts).1 q).quotient:ℝ)|≤
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  have hs : 0<(GeneralPaperSourceParameters.prepare k).summarySize := by
    rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
    positivity
  have hr (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
      (location r).val<cuts.read q ↔ r.val<((GeneralPaperRankCache.build k summary cuts).1.read q).val := by
    rw [hLocation]
    exact GeneralPaperRankCache.cached_spec k summary hMono cuts q r
  exact GeneralPaperEpochCachedQuery.rounded_cdf_error hn hs lambda k start count increment location delta hDelta hClose
    hCount hIncrement hMagnitude hVariation (cuts.read q) hCut ((GeneralPaperRankCache.build k summary cuts).1.read q) hr

theorem source_error {m : ℕ} (lambda k height start count : ℕ) (node : GeneralPaperIntervalCache.Node height)
    (increment : ℕ → Fin (2^height) → ℕ)
    (hHeight : height≤lambda+1) (hValid : GeneralPaperIntervalCache.Valid lambda k node)
    (hHistory : ∀ i, GeneralPaperIntervalLevels.levelAt node i.val=levels increment start i)
    (hStart : start≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (delta : ℕ → FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hDelta : ∀ t<count, ∀ r, (delta t).read r=increment (start+t) (GeneralPaperTreeEpochJoin.location lambda k height node r))
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code (Nat.two_pow_pos height) i)):ℝ)) (2^height-1)≤4)
    (cuts : FixedArrayTable m ℕ) (q : Fin m) (hCut : cuts.read q≤2^height) :
    let summary := GeneralPaperInitialSummary.build (prepare lambda k) (GeneralPaperQuantileComparison.width lambda k)
      (GeneralPaperSourceParameters.prepare k).summarySize height node
    |prefixMass (fun i => probability (GeneralPaperCachedMassJoin.base k) increment (start+count)
        (code (Nat.two_pow_pos height) i)) (cuts.read q)-
      (GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
        (GeneralPaperRankedCDFQuery.cached k (GeneralPaperEpochCachedQuery.prefixes (prepare lambda k) delta count)
          (GeneralPaperRankCache.build k summary cuts).1 q).quotient:ℝ)|≤
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
  have hPath := GeneralPaperTreeEpochJoin.history_path lambda k height start node increment hHistory hStart hIncrement
  exact cached_error (Nat.two_pow_pos height) lambda k start count increment _
    (GeneralPaperTreeEpochJoin.location lambda k height node) (fun _ => rfl)
    (GeneralPaperSummaryOrdered.summary_ordered lambda k height node hHeight hValid hPath) delta hDelta
    (GeneralPaperTreeEpochJoin.initial_history_close lambda k height start node increment hHeight hValid hHistory hStart hIncrement)
    hCount hIncrement hMagnitude hVariation cuts q hCut

end Blotto.GeneralPaperRankedEpochError
