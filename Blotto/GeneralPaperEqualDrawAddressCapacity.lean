import Blotto.GeneralPaperEqualFullInitializationResources

/-! The existing native draw reference is tested against the complete
retained representation, with separate route/segment/count/Boolean widths.
No reference change, runtime size query or new sampler is introduced. -/
namespace Blotto.GeneralPaperEqualDrawAddressCapacity
open GeneralPaperEqualRetainedStorage GeneralPaperEncodedBasisStorage
open GeneralPaperEqualNativeRetainedStorage (short)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

theorem twice_exponent : ∀ k : ℕ, 2 * k ≤ 2 ^ k := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    by_cases h : k = 0
    · subst k; decide
    · have hp : 2 ≤ 2 ^ k := by
        have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 1 ≤ k by omega)
        simpa only [pow_one] using hpow
      simp only [pow_succ]
      omega

theorem half_word (n : ℕ) : 2 * binaryWordWidth n ≤ n + 2 := by
  by_cases h : n = 0
  · subst n; decide
  · have hp : 2 ^ n.log2 ≤ n := (Nat.le_log2 h).mp le_rfl
    have hi := twice_exponent n.log2
    unfold binaryWordWidth
    omega

theorem word_le (n : ℕ) : binaryWordWidth n ≤ n + 1 := Nat.add_le_add_right (Nat.log2_le_self n) 1

theorem address_bounds (n m k b : ℕ) (hm : m ≤ 3) (hb : 3 ≤ b) :
    let q := short n k
    let C := n + m + k + 69
    let A := GeneralPaperEqualBitDrawRates.address n m k b
    A ≤ C + b ∧ A ≤ 16 * (b + q) ∧ q + 58 ≤ C ∧ 11 ≤ q := by
  let q := short n k
  let C := n + m + k + 69
  let A := GeneralPaperEqualBitDrawRates.address n m k b
  have hN := word_le n
  have hQ : q + 58 ≤ C := by dsimp [q, short, C]; omega
  have hQP : 11 ≤ q := by have h := binaryWordWidth_pos n; dsimp [q, short]; omega
  have hSize : GeneralPaperEqualBitDrawRates.word n k b = 67108864 * (b + q) := by
    unfold GeneralPaperEqualBitDrawRates.word GeneralPaperEqualBitDrawRates.size
    congr 1
    dsimp [q, short]
    omega
  have hA : A ≤ binaryWordWidth (C + 1) + binaryWordWidth (67108864 * (b + q) + 1) := by
    dsimp only [A, GeneralPaperEqualBitDrawRates.address]
    rw [hSize]
    exact StoredArrayReferenceList.poolAddressWidth_log_bound C _
  have hConst : binaryWordWidth 67108864 = 27 := by decide
  have hMul := binaryWordWidth_mul 67108864 (b + q)
  rw [hConst] at hMul
  have hOne : binaryWordWidth 1 = 1 := by decide
  have hAdd := GeneralPaperReferenceScaling.word_add (67108864 * (b + q)) 1
  rw [hOne] at hAdd
  have hHalfC := half_word (C + 1)
  have hHalfB := half_word (b + q)
  have hAC : A ≤ C + b := by omega
  have hC : binaryWordWidth (C + 1) ≤ binaryWordWidth n + binaryWordWidth (m + k + 70) := by
    have he : C + 1 = n + (m + k + 70) := by dsimp [C]; omega
    rw [he]
    exact GeneralPaperReferenceScaling.word_add n _
  have hTail := word_le (m + k + 70)
  have hB := word_le (b + q)
  have hAQ : A ≤ 16 * (b + q) := by dsimp [q, short] at *; omega
  exact ⟨hAC, hAQ, hQ, hQP⟩

def profile (A n k b : ℕ) : ℕ :=
  let q := short n k
  preparedProfile A n 3 7 (524288 * q) q (3670016 * q + 1) (3670016 * q + 3) b +
    cacheProfile A 7 (3670016 * q + 1) + k + 4 + 99 * A

theorem profile_eq (A n k b : ℕ) :
    profile A n k b = 66060288 * A * short n k + 121110528 * short n k +
      n * (17 * A + 2 * short n k + 6) + 2189 * A + b + k + 123 := by
  have h3 : binaryWordWidth 3 = 2 := by decide
  have h7 : binaryWordWidth 7 = 3 := by decide
  unfold profile preparedProfile segmentProfile cacheProfile wordProfile arrayProfile
  rw [h3, h7]
  ring

theorem profile_pool (n m k b : ℕ) (hm : m ≤ 3) (hb : 3 ≤ b) :
    profile (GeneralPaperEqualBitDrawRates.address n m k b) n k b ≤
      (n + m + k + 69) * GeneralPaperEqualBitDrawRates.word n k b := by
  let q := short n k
  let C := n + m + k + 69
  let A := GeneralPaperEqualBitDrawRates.address n m k b
  obtain ⟨hAC, hAQ, hQ, hQP⟩ := address_bounds n m k b hm hb
  change A ≤ C + b at hAC
  change A ≤ 16 * (b + q) at hAQ
  change q + 58 ≤ C at hQ
  change 11 ≤ q at hQP
  have hCP : 1 ≤ C := by omega
  have hn : n ≤ C := by dsimp [C]; omega
  have hk : k ≤ q := by dsimp [q, short]; omega
  have hScale : b + q ≤ C * (b + q) := Nat.le_mul_of_pos_left _ (by omega)
  have hN := Nat.mul_le_mul hn (show 17 * A + 2 * q + 6 ≤ 280 * (b + q) by omega)
  have hAM := Nat.mul_le_mul_left 2189 hAQ
  have hRest : b + k + 123 ≤ 16 * (b + q) := by omega
  have hOverhead : n * (17 * A + 2 * q + 6) + 2189 * A + b + k + 123 ≤ 131072 * C * (b + q) := by
    nlinarith only [hN, hAM, hRest, hScale]
  have hAprod := Nat.mul_le_mul_right q hAC
  have hGap := Nat.mul_le_mul_left b hQ
  have hCache : 66060288 * A * q + 3831496704 * b ≤ 66060288 * C * (q + b) := by
    nlinarith only [hAprod, hGap]
  rw [profile_eq]
  change 66060288 * A * q + 121110528 * q + n * (17 * A + 2 * q + 6) + 2189 * A + b + k + 123 ≤ _
  have hWord : GeneralPaperEqualBitDrawRates.word n k b = 67108864 * (b + q) := by
    unfold GeneralPaperEqualBitDrawRates.word GeneralPaperEqualBitDrawRates.size
    congr 1
    dsimp [q, short]
    omega
  rw [hWord]
  change _ ≤ C * (67108864 * (b + q))
  by_cases hBig : 132 ≤ C
  · have hHigh := Nat.mul_le_mul_right q (show 121110528 ≤ 917504 * C by omega)
    nlinarith only [hCache, hOverhead, hHigh, Nat.zero_le (C * b)]
  · have hLow : 121110528 * q ≤ 3831496704 * b := by omega
    nlinarith only [hCache, hOverhead, hLow, Nat.zero_le (C * (b + q))]

theorem capacity (n m k b : ℕ) (hm : m ≤ 3) (hb : 3 ≤ b) :
    profile (GeneralPaperEqualBitDrawRates.address n m k b) n k b <
      2 ^ GeneralPaperEqualBitDrawRates.address n m k b := by
  have h := profile_pool n m k b hm hb
  have hlt := lt_pow_binaryWordWidth ((n + m + k + 69) * (GeneralPaperEqualBitDrawRates.word n k b + 1) + 1)
  exact h.trans_lt ((by nlinarith : (n + m + k + 69) * GeneralPaperEqualBitDrawRates.word n k b <
    (n + m + k + 69) * (GeneralPaperEqualBitDrawRates.word n k b + 1) + 1).trans hlt)

end Blotto.GeneralPaperEqualDrawAddressCapacity
