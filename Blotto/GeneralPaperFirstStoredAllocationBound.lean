import Blotto.GeneralPaperFirstStoredContract

/-! Scalar majorants of complete stored postselection/rejection work for
any valid corrected grouped cache. Actual midpoint precision remains k+5;
only source heights and encoded categorical widths use the successor bound. -/
namespace Blotto.GeneralPaperFirstStoredAllocationBound
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperStoredDrawMajorant (bound groups_mono)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def nativeBound (model : RationalCostModel) (A n k b : ℕ) : ℕ :=
  bound model A n 3 (GeneralPaperStoredNativeRejectionBound.wordBound n (k+1))
    (3670016*GeneralPaperEqualNativeRetainedStorage.short n (k+1)+3) (k+5)
    (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b (binaryWordWidth n+k+10)

theorem allocation_bound {n : ℕ} (model : RationalCostModel) (W k b : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (small : ∀ j,2*(rounded true model W k values v hv).weight j≤1)
    (a : GeneralPaperEqualStoredBitSampler.Sampler (terminal (rounded true model W k values v hv) small).partition
      (lottery (rounded true model W k values v hv) small)) (hk : a.exponent=k) :
    GeneralPaperStoredAllocationWork.expectedBound model a.address (GeneralPaperEqualNativeSampler.segmentHeight n (k+1))
      b (binaryWordWidth n+k+10) a ≤ nativeBound model a.address n k b := by
  let m := (terminal (rounded true model W k values v hv) small).groups.length
  have hCount := GeneralPaperEqualFirstNativeCache.compact_count (rounded true model W k values v hv) small
  have hWidth : a.prepared.rangeBits ≤ GeneralPaperStoredNativeRejectionBound.wordBound n (k+1) := by
    simpa only [GeneralPaperStoredNativeRejectionBound.wordBound,Nat.add_assoc] using
      GeneralPaperEqualFirstHeights.rejection_range true model W k values v hv small a.prepared
  have hRows : a.categorical.rows.length ≤ 7 := by rw [GeneralPaperEqualBooleanCache.rows_length]; exact hCount.2
  have hReject := GeneralPaperStoredNativeRejectionBound.monotone model a.address a.prepared.rangeBits _ a.categorical.rows.length
    (GeneralPaperStoredNativeRejectionBound.wordBound n (k+1)) 7 7 hWidth hCount.2 hRows
  have hK : a.prepared.midpointBits=k+5 := a.exponent_correct.trans (congrArg (fun k => k+5) hk)
  have hMidpoint := GeneralPaperStoredSamplerMidpointWork.bound_le model a.address
    (3670016*GeneralPaperEqualNativeRetainedStorage.short n (k+1)+3) a.prepared
    (GeneralPaperEqualFirstDrawRepresentation.controls model W k values v hv small a hk)
  rw [hK] at hMidpoint
  have hCompare : GeneralPaperStoredAllocationWork.expectedBound model a.address
      (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b (binaryWordWidth n+k+10) a ≤
      bound model a.address n m (GeneralPaperStoredNativeRejectionBound.wordBound n (k+1))
        (3670016*GeneralPaperEqualNativeRetainedStorage.short n (k+1)+3) (k+5)
        (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b (binaryWordWidth n+k+10) := by
    unfold GeneralPaperStoredAllocationWork.expectedBound GeneralPaperStoredPostselectionWork.bound
      GeneralPaperStoredSamplerGroupsWork.drawBound bound
    rw [hK]
    dsimp only [m]
    omega
  exact hCompare.trans (groups_mono model a.address n m 3
    (GeneralPaperStoredNativeRejectionBound.wordBound n (k+1))
    (3670016*GeneralPaperEqualNativeRetainedStorage.short n (k+1)+3) (k+5)
    (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b (binaryWordWidth n+k+10)
    (GeneralPaperEqualFirstNativeCache.group_count _ small))

end Blotto.GeneralPaperFirstStoredAllocationBound
