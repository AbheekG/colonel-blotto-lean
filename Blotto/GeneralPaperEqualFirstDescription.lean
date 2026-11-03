import Blotto.GeneralPaperFirstAllExactRealSampling

/-! Every retained categorical/route/segment/control field is counted for
the corrected equal-budget source. The reference width is derived internally;
the original budget is owned once. This is a description, not a peak-lifetime
claim about preparation. -/
namespace Blotto.GeneralPaperEqualFirstDescription
open GeneralPaperEqualFirstRounding
open GeneralPaperEqualNativeRetainedStorage
open GeneralPaperEqualRetainedStorage
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem controls {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1)
    (a : GeneralPaperEqualStoredBitSampler.Sampler
      (GeneralPaperEqualFiniteKernel.terminal (rounded true model W k values v hv) small).partition
      (GeneralPaperEqualFiniteKernel.lottery (rounded true model W k values v hv) small)) (hk : a.exponent = k) :
    ∀ x ∈ [a.prepared.D, a.prepared.rangeBits, a.prepared.midpointBits, a.prepared.midpointCount],
      GeneralPaperEncodedScalarStorage.natBits x ≤ height n (k+1) := by
  let p := a.prepared
  have hD := GeneralPaperEqualFirstHeights.categorical_denominator true model W k values v hv small p
  have hR := GeneralPaperEqualFirstHeights.rejection_range true model W k values v hv small p
  have hK : p.midpointBits = k+5 := a.exponent_correct.trans (congrArg (fun k => k+5) hk)
  have hCount := GeneralPaperEqualPreparedCache.midpointCount_word p
  change ∀ x ∈ [p.D, p.rangeBits, p.midpointBits, p.midpointCount],
    GeneralPaperEncodedScalarStorage.natBits x ≤ height n (k+1)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · unfold GeneralPaperEncodedScalarStorage.natBits height short
    omega
  · have h := natBits_bound p.rangeBits
    unfold height short
    omega
  · have h := natBits_bound p.midpointBits
    unfold height short
    omega
  · unfold GeneralPaperEncodedScalarStorage.natBits height short
    omega

theorem profile_bound {n : ℕ} (model : RationalCostModel) (Wv W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model Wv k values v hv).weight j ≤ 1) (budget : ℚ)
    (a : GeneralPaperEqualStoredBitSampler.Sampler
      (GeneralPaperEqualFiniteKernel.terminal (rounded true model Wv k values v hv) small).partition
      (GeneralPaperEqualFiniteKernel.lottery (rounded true model Wv k values v hv) small))
    (hk : a.exponent = k) (hB : a.prepared.budget = budget) :
    footprint W a ≤ profile W n (k+1) (rationalWordWidth budget) := by
  have hD := GeneralPaperEqualFirstHeights.categorical_denominator true model Wv k values v hv small a.prepared
  have hCount (i) : binaryWordWidth (a.prepared.counts.read i) ≤
      3670016*(binaryWordWidth n+k+11)+1 :=
    (binaryWordWidth_mono (GeneralPaperEqualPreparedCache.counts_bounded a.prepared i)).trans hD
  have h := stored_bound W a
    (GeneralPaperEqualFirstHeights.lottery_height true model Wv k values v hv small)
    (GeneralPaperEqualFirstHeights.route_height true model Wv k values v hv small a.prepared)
    hCount (controls model Wv k values v hv small a hk)
  have hm := GeneralPaperEqualNativeCache.group_count (rounded true model Wv k values v hv) small
  have hr := (GeneralPaperEqualNativeCache.compact_count (rounded true model Wv k values v hv) small).2
  have hs : GeneralPaperEqualNativeSampler.segmentHeight n (k+1) ≤ height n (k+1) := by
    have h0 := GeneralPaperEqualNativeCache.segment_height_bound n (k+1)
    unfold height short
    omega
  have hc : binaryWordWidth n+k+10 ≤ height n (k+1) := by unfold height short; omega
  have hd : 3670016*(binaryWordWidth n+k+11)+1 ≤ height n (k+1) := by unfold height short; omega
  have hR := GeneralPaperEqualFirstHeights.rejection_range true model Wv k values v hv small a.prepared
  have hP := preparedProfile_mono W n (rationalWordWidth budget) hm hr hs hc hd
    (le_rfl : height n (k+1) ≤ height n (k+1))
  have hC := cacheProfile_mono W hr (hR.trans hd)
  have hA := (GeneralPaperEqualBitDrawRates.metadata_bounds n _ k (rationalWordWidth budget) hm).1
  have hAddress : a.address ≤ 2*GeneralPaperEqualBitDrawRates.log n (k+1) (rationalWordWidth budget) := by
    rw [a.address_correct, hk, hB]
    exact hA.trans (Nat.mul_le_mul_left 2 (GeneralPaperEqualFirstBitWork.log_step n k (rationalWordWidth budget)))
  have hNat := natBits_bound a.address
  have hK : GeneralPaperEncodedScalarStorage.natBits a.exponent ≤ k+2 := by rw [hk]; exact natBits_bound k
  rw [hB] at h
  unfold profile
  omega

theorem paper_description {n : ℕ} (model : RationalCostModel) (Wv k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model Wv k values v hv).weight j ≤ 1) (budget : ℚ)
    (a : GeneralPaperEqualStoredBitSampler.Sampler
      (GeneralPaperEqualFiniteKernel.terminal (rounded true model Wv k values v hv) small).partition
      (GeneralPaperEqualFiniteKernel.lottery (rounded true model Wv k values v hv) small))
    (hk : a.exponent = k) (hB : a.prepared.budget = budget) :
    let b := rationalWordWidth budget
    let R := GeneralPaperEqualDescriptionRates.reference n (k+1) b
    footprint R a ≤ GeneralPaperEqualDescriptionRates.paperBound n (k+1) b ∧ footprint R a < 2^R := by
  dsimp only
  let R := GeneralPaperEqualDescriptionRates.reference n (k+1) (rationalWordWidth budget)
  have h := (profile_bound model Wv R k values v hv small budget a hk hB).trans
    (GeneralPaperEqualDescriptionRates.profile_bound R n (k+1) (rationalWordWidth budget))
  exact ⟨h.trans (GeneralPaperEqualDescriptionRates.bound_at_reference n (k+1) (rationalWordWidth budget)),
    h.trans_lt (GeneralPaperEqualDescriptionRates.capacity n (k+1) (rationalWordWidth budget))⟩

end Blotto.GeneralPaperEqualFirstDescription
