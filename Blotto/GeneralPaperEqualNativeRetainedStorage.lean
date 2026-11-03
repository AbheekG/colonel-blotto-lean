import Blotto.GeneralPaperEqualRetainedStorage

/-! Native bounds for every retained field, including the Boolean lists and
all stored controls. Original budget precision occurs once in the payload.
The reference parameter prices representation metadata, not a supplied size
certificate or an execution input. -/
namespace Blotto.GeneralPaperEqualNativeRetainedStorage
open GeneralPaperEqualRetainedStorage GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperEqualNativeSampler (rounded segmentHeight)
open GeneralPaperEqualStoredBitSampler (native)
open GeneralPaperPositiveSegmentCompaction (count)
open GeneralPaperEqualFiniteKernel (terminal lottery)
set_option autoImplicit false
set_option maxHeartbeats 1200000

def short (n k : ℕ) : ℕ := binaryWordWidth n + k + 10
def height (n k : ℕ) : ℕ := 8388608 * short n k

theorem natBits_bound (a : ℕ) : natBits a ≤ a + 2 := by
  have h := Nat.log2_le_self a
  unfold natBits binaryWordWidth
  omega

theorem segmentProfile_mono (W : ℕ) {m r s M R S : ℕ} (hm : m ≤ M) (hr : r ≤ R) (hs : s ≤ S) :
    segmentProfile W m r s ≤ segmentProfile W M R S := by
  unfold segmentProfile arrayProfile
  gcongr

theorem preparedProfile_mono (W n b : ℕ) {m r s c d P M R S C D Q : ℕ}
    (hm : m ≤ M) (hr : r ≤ R) (hs : s ≤ S) (hc : c ≤ C) (hd : d ≤ D) (hp : P ≤ Q) :
    preparedProfile W n m r s c d P b ≤ preparedProfile W n M R S C D Q b := by
  have hw := binaryWordWidth_mono hm
  have hl := segmentProfile_mono W hm hr hs
  unfold preparedProfile arrayProfile
  nlinarith only [hl, Nat.mul_le_mul_left n hw, Nat.mul_le_mul_left n hc,
    Nat.mul_le_mul hr (Nat.add_le_add_left hd (W + 1)), hp]

theorem cacheProfile_mono (W : ℕ) {r w R V : ℕ} (hr : r ≤ R) (hw : w ≤ V) :
    cacheProfile W r w ≤ cacheProfile W R V := by
  have hWord := binaryWordWidth_mono hr
  unfold cacheProfile wordProfile
  gcongr

theorem native_controls {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let p := (native bits model W k values v hv small budget).prepared
    ∀ x ∈ [p.D, p.rangeBits, p.midpointBits, p.midpointCount], natBits x ≤ height n k := by
  dsimp only
  let p := (native bits model W k values v hv small budget).prepared
  have hD := GeneralPaperEqualNativeCache.denominator_word bits model W k values v hv small budget
  have hR := GeneralPaperEqualNativeCache.rangeBits bits model W k values v hv small budget
  have hK : p.midpointBits = k + 5 := rfl
  have hCount := GeneralPaperEqualPreparedCache.midpointCount_word p
  change binaryWordWidth p.D ≤ _ at hD
  change p.rangeBits ≤ _ at hR
  change ∀ x ∈ [p.D, p.rangeBits, p.midpointBits, p.midpointCount], natBits x ≤ height n k
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · unfold natBits height short
    omega
  · have h := natBits_bound p.rangeBits
    unfold height short
    omega
  · rw [hK]
    have h := natBits_bound (k + 5)
    unfold height short
    omega
  · unfold natBits
    unfold height short
    omega

def profile (W n k b : ℕ) : ℕ :=
  preparedProfile W n 3 7 (height n k) (height n k) (height n k) (height n k) b +
    cacheProfile W 7 (height n k) + k + 2 + 2 * GeneralPaperEqualBitDrawRates.log n k b + 2 + 98 * W

theorem native_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (Wv W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model Wv k values v hv).weight j ≤ 1) (budget : ℚ) :
    footprint W (native bits model Wv k values v hv small budget) ≤ profile W n k (rationalWordWidth budget) := by
  let a := native bits model Wv k values v hv small budget
  have h := stored_bound W a (GeneralPaperEqualNativeSampler.native_lottery_height bits model Wv k values v hv small)
    (GeneralPaperEqualNativeCache.route_height bits model Wv k values v hv small budget)
    (GeneralPaperEqualNativeCache.count_word bits model Wv k values v hv small budget)
    (native_controls bits model Wv k values v hv small budget)
  have hm := GeneralPaperEqualNativeCache.group_count (rounded bits model Wv k values v hv) small
  have hr := (GeneralPaperEqualNativeCache.compact_count (rounded bits model Wv k values v hv) small).2
  have hs : segmentHeight n k ≤ height n k := by
    have h0 := GeneralPaperEqualNativeCache.segment_height_bound n k
    unfold height short
    omega
  have hc : binaryWordWidth n + k + 9 ≤ height n k := by unfold height short; omega
  have hd : 3670016 * (binaryWordWidth n + k + 10) + 1 ≤ height n k := by unfold height short; omega
  have hR := GeneralPaperEqualNativeCache.rangeBits bits model Wv k values v hv small budget
  have hP := preparedProfile_mono W n (rationalWordWidth budget) hm hr hs hc hd (le_rfl : height n k ≤ height n k)
  have hC := cacheProfile_mono W hr (hR.trans hd)
  change cacheProfile W _ a.prepared.rangeBits ≤ _ at hC
  have hA := (GeneralPaperEqualBitDrawRates.metadata_bounds n _ k (rationalWordWidth budget) hm).1
  have hNat := natBits_bound a.address
  have hK : natBits a.exponent ≤ k + 2 := natBits_bound k
  have hBudget : a.prepared.budget = budget := rfl
  rw [hBudget] at h
  change a.address ≤ _ at hA
  change footprint W a ≤ _
  unfold profile
  omega

end Blotto.GeneralPaperEqualNativeRetainedStorage
