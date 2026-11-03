import Blotto.GeneralPaperActualEpochCacheStorage

/-! Every local epoch prefix reserves the full period's row references.
The recorded rows are the actual pre-update candidates; code words and
fixed row sizes bound their payload without rerunning a selector. -/
namespace Blotto.GeneralPaperLocalTrajectoryStorage
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def profile (W m lambda k : ℕ) : ℕ :=
  (GeneralPaperTrajectoryParameters.prepare lambda k).period*
    (m*GeneralPaperDecoderControls.operandWidth lambda+m*W+65*W)+64*W

theorem selected {m k : ℕ} (W Qv : ℕ) (cache : Cache m k) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (hc : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
    GeneralPaperEncodedTrajectoryStorage.footprint W (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period
      (GeneralPaperCatalogueEpoch.execute cache current.powers current.profit current.T weights Bc Br (initial cache) count).2≤
        profile W m cache.alphabet.lambda k := by
  let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
  let rows := (GeneralPaperCatalogueEpoch.execute cache current.powers current.profit current.T weights Bc Br (initial cache) count).2
  let L := GeneralPaperDecoderControls.operandWidth cache.alphabet.lambda
  let P := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period
  have hSize : rows.size=count := GeneralPaperCatalogueEpoch.trajectory_size _ _ _ _ _ _ _ _ _
  have hPayload : GeneralPaperRetainedTrajectoryBits.trajectoryBits rows≤count*(m*L) := by
    have h := GeneralPaperRetainedTrajectoryBits.trajectory_bound rows L (by
      intro i
      apply GeneralPaperRetainedTrajectoryBits.row_bound
      intro j
      have hi : i.val<count := lt_of_lt_of_eq i.isLt hSize
      change 1+binaryWordWidth (((GeneralPaperCatalogueEpoch.execute cache current.powers current.profit current.T weights Bc Br (initial cache) count).2[i.val]).read j)≤L
      rw [GeneralPaperCatalogueEpoch.trajectory_read cache current.powers current.profit current.T weights Bc Br (initial cache) count i.val hi]
      exact GeneralPaperRetainedTrajectoryBits.candidate_word cache _ _ _ _ _ _ _ j)
    rw [hSize] at h
    exact h
  have hCount : count≤P := hc
  have hp := Nat.mul_le_mul_right (m*L) hCount
  have hr := Nat.mul_le_mul_right (m*W+64*W) hCount
  change GeneralPaperEncodedTrajectoryStorage.footprint W P rows≤P*(m*L+m*W+65*W)+64*W
  unfold GeneralPaperEncodedTrajectoryStorage.footprint
  rw [hSize]
  nlinarith only [hPayload,hp,hr]

theorem priced {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (ht : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
    let period := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period
    GeneralPaperEncodedTrajectoryStorage.footprint W period
      (GeneralPaperLocalEpochExecution.execute bits index price W c cache current.profit current.T weights Bc Br period count).1.2≤
        profile W m cache.alphabet.lambda k := by
  dsimp only
  rw [GeneralPaperSelectedLocalEpochExecution.data bits index price W Qv cache c hc weights Bc Br _ count]
  exact selected W Qv cache weights Bc Br count ht

end Blotto.GeneralPaperLocalTrajectoryStorage
