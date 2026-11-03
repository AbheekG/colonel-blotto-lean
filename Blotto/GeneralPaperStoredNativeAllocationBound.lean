import Blotto.GeneralPaperStoredDrawMajorant

/-! The native scalar-majorant comparison is independent of installed
memory. It therefore also applies after outer writes preserve inner readback. -/
namespace Blotto.GeneralPaperStoredNativeAllocationBound
open GeneralPaperStoredDrawMajorant (bound groups_mono)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

theorem native_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    GeneralPaperStoredAllocationWork.expectedBound model source.address (GeneralPaperEqualNativeSampler.segmentHeight n k)
      (rationalWordWidth budget) (binaryWordWidth n + k + 9) source ≤
      GeneralPaperStoredDrawMajorant.nativeBound model source.address n k (rationalWordWidth budget) := by
  dsimp only
  let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
  let m := (GeneralPaperEqualFiniteKernel.terminal (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv) small).groups.length
  have hCount := GeneralPaperEqualNativeCache.compact_count (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv) small
  have hWidth := GeneralPaperEqualNativeCache.rangeBits bits model W k values v hv small budget
  have hRows : source.categorical.rows.length ≤ 7 := by rw [GeneralPaperEqualBooleanCache.rows_length]; exact hCount.2
  have hReject := GeneralPaperStoredNativeRejectionBound.monotone model source.address source.prepared.rangeBits _ source.categorical.rows.length
    (GeneralPaperStoredNativeRejectionBound.wordBound n k) 7 7 hWidth hCount.2 hRows
  have hMidpoint := GeneralPaperStoredSamplerMidpointWork.native_majorant bits model W k values v hv small budget
  change GeneralPaperStoredSamplerMidpointWork.bound model source.address source.prepared ≤
    GeneralPaperStoredSamplerMidpointWork.majorant model source.address (3670016 * GeneralPaperEqualNativeRetainedStorage.short n k + 3) (k + 5) at hMidpoint
  have hK : source.prepared.midpointBits = k + 5 := rfl
  have hCompare : GeneralPaperStoredAllocationWork.expectedBound model source.address
      (GeneralPaperEqualNativeSampler.segmentHeight n k) (rationalWordWidth budget) (binaryWordWidth n + k + 9) source ≤
      bound model source.address n m (GeneralPaperStoredNativeRejectionBound.wordBound n k)
        (3670016 * GeneralPaperEqualNativeRetainedStorage.short n k + 3) (k + 5)
        (GeneralPaperEqualNativeSampler.segmentHeight n k) (rationalWordWidth budget) (binaryWordWidth n + k + 9) := by
    unfold GeneralPaperStoredAllocationWork.expectedBound GeneralPaperStoredPostselectionWork.bound
      GeneralPaperStoredSamplerGroupsWork.drawBound bound
    rw [hK]
    dsimp only [m]
    omega
  have hGroups := groups_mono model source.address n m 3 (GeneralPaperStoredNativeRejectionBound.wordBound n k)
    (3670016 * GeneralPaperEqualNativeRetainedStorage.short n k + 3) (k + 5)
    (GeneralPaperEqualNativeSampler.segmentHeight n k) (rationalWordWidth budget) (binaryWordWidth n + k + 9)
    (GeneralPaperEqualNativeCache.group_count _ small)
  exact hCompare.trans hGroups

end Blotto.GeneralPaperStoredNativeAllocationBound
