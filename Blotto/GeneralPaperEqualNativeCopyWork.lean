import Blotto.GeneralPaperEqualCopyPriceMonotone

/-! Native copied cache dimensions/field sizes are derived from the actual
rounded producer. No source-family cost or size certificate is supplied.
The original budget occurs once in the copy price. -/
namespace Blotto.GeneralPaperEqualNativeCopyWork
open GeneralPaperEqualNativeRetainedStorage (height short)
open GeneralPaperEqualBitDrawRates (log)
open GeneralPaperEqualNativeSampler (rounded segmentHeight)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def profile (S n k b : ℕ) : ℕ :=
  GeneralPaperEqualSamplerCopy.price S (2 * log n k b) n 3 7
    (height n k) (height n k) (height n k) (height n k) b (height n k) k (2 * log n k b)

theorem native {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let a := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
    (GeneralPaperEqualSamplerCopy.run S a.address a).2 ≤ profile S n k (rationalWordWidth budget) := by
  dsimp only
  let a := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
  have h := GeneralPaperEqualSamplerCopy.work S a.address a
    (GeneralPaperPositiveSegmentCompaction.compact_height _
      (GeneralPaperEqualNativeSampler.native_lottery_height true model W k values v hv small))
    (GeneralPaperEqualNativeCache.route_height true model W k values v hv small budget)
    (GeneralPaperEqualNativeCache.count_word true model W k values v hv small budget)
    (GeneralPaperEqualNativeRetainedStorage.native_controls true model W k values v hv small budget)
  have hm := GeneralPaperEqualNativeCache.group_count (rounded true model W k values v hv) small
  have hr := (GeneralPaperEqualNativeCache.compact_count (rounded true model W k values v hv) small).2
  have hA := (GeneralPaperEqualBitDrawRates.metadata_bounds n _ k (rationalWordWidth budget) hm).1
  change a.address ≤ 2 * log n k (rationalWordWidth budget) at hA
  have hs : segmentHeight n k ≤ height n k := by
    have hx := GeneralPaperEqualNativeCache.segment_height_bound n k
    dsimp only [height,short]
    omega
  have hc : binaryWordWidth n + k + 9 ≤ height n k := by dsimp only [height,short]; omega
  have hd : 3670016 * (binaryWordWidth n + k + 10) + 1 ≤ height n k := by dsimp only [height,short]; omega
  have hw := (GeneralPaperEqualNativeCache.rangeBits true model W k values v hv small budget).trans hd
  apply h.trans
  unfold profile
  exact GeneralPaperEqualCopyPriceMonotone.sampler S n (rationalWordWidth budget) k
    hA hm hr hs hc hd le_rfl hw hA

end Blotto.GeneralPaperEqualNativeCopyWork
