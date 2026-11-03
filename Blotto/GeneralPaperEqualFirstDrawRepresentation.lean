import Blotto.GeneralPaperEqualFirstDrawCapacity

/-! The corrected rational/Boolean cache fits its actual compact draw
reference. All retained field sizes are derived from the actual c=256 source.
The source-only successor envelope does not change midpoint k+5 or addresses. -/
namespace Blotto.GeneralPaperEqualFirstDrawRepresentation
open GeneralPaperEqualFirstNativeFacts (rounded segmentHeight)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperEqualRetainedStorage
open GeneralPaperEqualNativeRetainedStorage (short)
open GeneralPaperEncodedScalarStorage (natBits)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem controls {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1)
    (a : GeneralPaperEqualStoredBitSampler.Sampler (terminal (rounded true model W k values v hv) small).partition
      (lottery (rounded true model W k values v hv) small)) (hk : a.exponent = k) :
    ∀ x ∈ [a.prepared.D,a.prepared.rangeBits,a.prepared.midpointBits,a.prepared.midpointCount],
      natBits x ≤ 3670016*short n (k+1)+3 := by
  let p := a.prepared
  have hD := GeneralPaperEqualFirstHeights.categorical_denominator true model W k values v hv small p
  have hR := GeneralPaperEqualFirstHeights.rejection_range true model W k values v hv small p
  have hK : p.midpointBits = k+5 := a.exponent_correct.trans (congrArg (fun k => k+5) hk)
  have hCount := GeneralPaperEqualPreparedCache.midpointCount_word p
  change ∀ x ∈ [p.D,p.rangeBits,p.midpointBits,p.midpointCount], natBits x ≤ _
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · unfold natBits short; omega
  · have h := GeneralPaperNaturalScalarLifetime.counter_word p.rangeBits
    unfold short; omega
  · have h := GeneralPaperNaturalScalarLifetime.counter_word p.midpointBits
    unfold short; omega
  · unfold natBits short; omega

theorem profile_bound {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (a : GeneralPaperEqualStoredBitSampler.Sampler (terminal (rounded true model W k values v hv) small).partition
      (lottery (rounded true model W k values v hv) small)) (hk : a.exponent = k) (hB : a.prepared.budget = budget) :
    footprint a.address a ≤ GeneralPaperEqualDrawAddressCapacity.profile a.address n (k+1) (rationalWordWidth budget) := by
  let A := a.address
  let q := short n (k+1)
  have hD := GeneralPaperEqualFirstHeights.categorical_denominator true model W k values v hv small a.prepared
  have h := stored_bound (s := segmentHeight n k) (c := q) (d := 3670016*q+1) (P := 3670016*q+3) A a
    (GeneralPaperEqualFirstNativeFacts.native_lottery_height true model W k values v hv small)
    (fun j => (GeneralPaperEqualFirstSourceOwnership.route_height true model W k values v hv small a.prepared.routes j).mono
      (by dsimp [q,short]; omega))
    (fun i => (binaryWordWidth_mono (GeneralPaperEqualPreparedCache.counts_bounded a.prepared i)).trans
      (by dsimp [q,short]; omega)) (controls model W k values v hv small a hk)
  have hm := GeneralPaperEqualFirstNativeCache.group_count (rounded true model W k values v hv) small
  have hr := (GeneralPaperEqualFirstNativeCache.compact_count (rounded true model W k values v hv) small).2
  have hs := GeneralPaperEqualFirstNativeCache.segment_height_bound n k
  have hP := GeneralPaperEqualNativeRetainedStorage.preparedProfile_mono A n (rationalWordWidth budget) hm hr
    (show segmentHeight n k ≤ 524288*q by dsimp [q,short]; omega)
    (le_rfl : q ≤ q) (le_rfl : 3670016*q+1 ≤ 3670016*q+1) (le_rfl : 3670016*q+3 ≤ 3670016*q+3)
  have hR := GeneralPaperEqualFirstHeights.rejection_range true model W k values v hv small a.prepared
  have hC := GeneralPaperEqualNativeRetainedStorage.cacheProfile_mono A hr
    (show a.prepared.rangeBits ≤ 3670016*q+1 by dsimp [q,short]; omega)
  have hNat : natBits a.address ≤ A+2 := GeneralPaperNaturalScalarLifetime.counter_word a.address
  have hK : natBits a.exponent ≤ k+2 := by rw [hk]; exact GeneralPaperNaturalScalarLifetime.counter_word k
  rw [hB] at h
  unfold GeneralPaperEqualDrawAddressCapacity.profile
  change footprint A a ≤ preparedProfile A n 3 7 (524288*q) q (3670016*q+1) (3670016*q+3)
    (rationalWordWidth budget)+cacheProfile A 7 (3670016*q+1)+(k+1)+4+99*A
  omega

theorem capacity {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (a : GeneralPaperEqualStoredBitSampler.Sampler (terminal (rounded true model W k values v hv) small).partition
      (lottery (rounded true model W k values v hv) small)) (hk : a.exponent = k) (hB : a.prepared.budget = budget) :
    footprint a.address a < 2^a.address := by
  have h := profile_bound model W k values v hv small budget a hk hB
  have ha : a.address = GeneralPaperEqualBitDrawRates.address n
      (terminal (rounded true model W k values v hv) small).groups.length k (rationalWordWidth budget) := by
    rw [a.address_correct,hk,hB]
  have hc := GeneralPaperEqualFirstDrawCapacity.capacity n
    (terminal (rounded true model W k values v hv) small).groups.length k (rationalWordWidth budget)
    (GeneralPaperEqualFirstNativeCache.group_count _ small) (GeneralPaperEqualNativeDrawRepresentation.budget_width budget)
  rw [← ha] at hc
  exact h.trans_lt hc

end Blotto.GeneralPaperEqualFirstDrawRepresentation
