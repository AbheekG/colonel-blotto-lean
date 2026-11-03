import Blotto.GeneralPaperEqualDrawAddressCapacity

/-! The complete actual native returned cache fits its own computed draw
reference, including retained rational/Boolean data and all control fields.
The prepared data and sampling routine are unchanged. Allocation/layout and
original-input pipeline composition are joined separately. -/
namespace Blotto.GeneralPaperEqualNativeDrawRepresentation
open GeneralPaperEncodedScalarStorage (natBits)
open GeneralPaperEqualRetainedStorage
open GeneralPaperEqualNativeRetainedStorage (short)
open GeneralPaperEqualNativeSampler (rounded segmentHeight)
open GeneralPaperEqualStoredBitSampler (native)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

theorem budget_width (budget : ℚ) : 3 ≤ rationalWordWidth budget := by
  have hn := binaryWordWidth_pos budget.num.natAbs
  have hd := binaryWordWidth_pos budget.den
  unfold rationalWordWidth
  omega

theorem native_controls {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let p := (native bits model W k values v hv small budget).prepared
    ∀ x ∈ [p.D, p.rangeBits, p.midpointBits, p.midpointCount], natBits x ≤ 3670016 * short n k + 3 := by
  dsimp only
  let p := (native bits model W k values v hv small budget).prepared
  have hD := GeneralPaperEqualNativeCache.denominator_word bits model W k values v hv small budget
  have hR := GeneralPaperEqualNativeCache.rangeBits bits model W k values v hv small budget
  have hK : p.midpointBits = k + 5 := rfl
  have hCount := GeneralPaperEqualPreparedCache.midpointCount_word p
  change binaryWordWidth p.D ≤ 3670016 * short n k + 1 at hD
  change p.rangeBits ≤ 3670016 * short n k + 1 at hR
  change ∀ x ∈ [p.D, p.rangeBits, p.midpointBits, p.midpointCount], natBits x ≤ _
  have hShort : k + 7 ≤ 3670016 * short n k + 3 := by unfold short; omega
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · unfold natBits; omega
  · have h := GeneralPaperNaturalScalarLifetime.counter_word p.rangeBits
    omega
  · have h := GeneralPaperNaturalScalarLifetime.counter_word p.midpointBits
    omega
  · unfold natBits
    omega

theorem native_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let a := native bits model W k values v hv small budget
    footprint a.address a ≤ GeneralPaperEqualDrawAddressCapacity.profile a.address n k (rationalWordWidth budget) := by
  dsimp only
  let a := native bits model W k values v hv small budget
  let A := a.address
  let q := short n k
  have h := stored_bound (s := segmentHeight n k) (c := short n k)
    (d := 3670016 * short n k + 1) (P := 3670016 * short n k + 3)
    A a (GeneralPaperEqualNativeSampler.native_lottery_height bits model W k values v hv small)
    (fun j => (GeneralPaperEqualNativeCache.route_height bits model W k values v hv small budget j).mono (by unfold short; omega))
    (GeneralPaperEqualNativeCache.count_word bits model W k values v hv small budget)
    (native_controls bits model W k values v hv small budget)
  have hm := GeneralPaperEqualNativeCache.group_count (rounded bits model W k values v hv) small
  have hr := (GeneralPaperEqualNativeCache.compact_count (rounded bits model W k values v hv) small).2
  have hs := GeneralPaperEqualNativeCache.segment_height_bound n k
  have hP := GeneralPaperEqualNativeRetainedStorage.preparedProfile_mono A n (rationalWordWidth budget)
    hm hr hs (le_rfl : q ≤ q) (le_rfl : 3670016 * q + 1 ≤ 3670016 * q + 1)
    (le_rfl : 3670016 * q + 3 ≤ 3670016 * q + 3)
  have hR := GeneralPaperEqualNativeCache.rangeBits bits model W k values v hv small budget
  have hC := GeneralPaperEqualNativeRetainedStorage.cacheProfile_mono A hr hR
  change cacheProfile A _ a.prepared.rangeBits ≤ cacheProfile A 7 (3670016 * q + 1) at hC
  have hNat := GeneralPaperNaturalScalarLifetime.counter_word a.address
  have hK : natBits a.exponent ≤ k + 2 := GeneralPaperNaturalScalarLifetime.counter_word k
  have hBudget : a.prepared.budget = budget := rfl
  rw [hBudget] at h
  change footprint A a ≤ GeneralPaperEqualDrawAddressCapacity.profile A n k (rationalWordWidth budget)
  unfold GeneralPaperEqualDrawAddressCapacity.profile
  change footprint A a ≤ preparedProfile A n 3 7 (524288 * q) q (3670016 * q + 1) (3670016 * q + 3)
    (rationalWordWidth budget) + cacheProfile A 7 (3670016 * q + 1) + k + 4 + 99 * A
  change natBits a.address ≤ A + 2 at hNat
  dsimp only [q, short] at h hP hC ⊢
  omega

theorem native_capacity {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let a := native bits model W k values v hv small budget
    footprint a.address a < 2 ^ a.address := by
  dsimp only
  let a := native bits model W k values v hv small budget
  have h := native_bound bits model W k values v hv small budget
  have hm := GeneralPaperEqualNativeCache.group_count (rounded bits model W k values v hv) small
  exact h.trans_lt (GeneralPaperEqualDrawAddressCapacity.capacity n _ k (rationalWordWidth budget) hm (budget_width budget))

theorem addressed_capacity {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let a := (GeneralPaperEqualAddressedPreparation.run bits model W A k values v hv small budget).1
    footprint a.address a < 2 ^ a.address := by
  dsimp only
  rw [GeneralPaperEqualAddressedPreparation.data]
  exact native_capacity bits model W k values v hv small budget

end Blotto.GeneralPaperEqualNativeDrawRepresentation
