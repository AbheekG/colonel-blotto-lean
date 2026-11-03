import Blotto.GeneralPaperEqualFirstPreparationSpaceRates

/-! The existing compact draw reference also fits the corrected source's
one-larger size envelope. No address or executed midpoint precision changes.
The proof uses the slack in the actual fixed pool/reference formula. -/
namespace Blotto.GeneralPaperEqualFirstDrawCapacity
open GeneralPaperEqualBitDrawRates (address word)
open GeneralPaperEqualNativeRetainedStorage (short)
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem eighth_power : ∀ r : ℕ, 8*(r+1) ≤ 2^r+24 := by
  intro r
  induction r with
  | zero => decide
  | succ r ih =>
    by_cases h : r ≤ 2
    · interval_cases r <;> norm_num
    · have hp : 8 ≤ 2^r := by
        have hPow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 3 ≤ r by omega)
        simpa using hPow
      rw [pow_succ]
      omega

theorem eighth_word (n : ℕ) : 8*binaryWordWidth n ≤ n+24 := by
  by_cases h : n = 0
  · subst n; decide
  · have hp : 2^n.log2 ≤ n := (Nat.le_log2 h).mp le_rfl
    have hi := eighth_power n.log2
    unfold binaryWordWidth
    omega

theorem address_fraction (n m k b : ℕ) (hm : m ≤ 3) (hb : 3 ≤ b) :
    4*address n m k b ≤ 3*((n+m+k+69)+b) := by
  let q := short n k
  let C := n+m+k+69
  let A := address n m k b
  obtain ⟨_,_,hQ,hQP⟩ := GeneralPaperEqualDrawAddressCapacity.address_bounds n m k b hm hb
  change q+58 ≤ C at hQ
  change 11 ≤ q at hQP
  have hSize : word n k b = 67108864*(b+q) := by unfold word GeneralPaperEqualBitDrawRates.size; dsimp [q,short]; omega
  have hA : A ≤ binaryWordWidth (C+1)+binaryWordWidth (67108864*(b+q)+1) := by
    dsimp only [A,address]
    rw [hSize]
    exact StoredArrayReferenceList.poolAddressWidth_log_bound C _
  have hMul := binaryWordWidth_mul 67108864 (b+q)
  have hAdd := GeneralPaperReferenceScaling.word_add (67108864*(b+q)) 1
  have hConst : binaryWordWidth 67108864 = 27 := by decide
  have hOne : binaryWordWidth 1 = 1 := by decide
  rw [hConst] at hMul
  rw [hOne] at hAdd
  have hC := eighth_word (C+1)
  have hB := eighth_word (b+q)
  change 4*A ≤ 3*(C+b)
  omega

theorem profile_pool (n m k b : ℕ) (hm : m ≤ 3) (hb : 3 ≤ b) :
    GeneralPaperEqualDrawAddressCapacity.profile (address n m k b) n (k+1) b ≤
      (n+m+k+69)*word n k b := by
  let q := short n k
  let C := n+m+k+69
  let A := address n m k b
  obtain ⟨hAC,hAQ,hQ,hQP⟩ := GeneralPaperEqualDrawAddressCapacity.address_bounds n m k b hm hb
  change A ≤ C+b at hAC
  change A ≤ 16*(b+q) at hAQ
  change q+58 ≤ C at hQ
  change 11 ≤ q at hQP
  have hFraction : 4*A ≤ 3*(C+b) := address_fraction n m k b hm hb
  have hAprod := Nat.mul_le_mul_right (q+1) hFraction
  have hbq := Nat.mul_le_mul_left b (show q ≤ C by omega)
  have hcq := Nat.mul_le_mul_left C (show 6 ≤ q by omega)
  have hbc := Nat.mul_le_mul_left b (show 6 ≤ C by omega)
  have hCore : 8*A*(q+1) ≤ 7*C*(b+q) := by nlinarith only [hAprod,hbq,hcq,hbc]
  have hCache := Nat.mul_le_mul_left 66060288 hCore
  have hn : n ≤ C := by dsimp [C]; omega
  have hk : k ≤ q := by dsimp [q,short]; omega
  have hScale : b+q ≤ C*(b+q) := Nat.le_mul_of_pos_left _ (by omega)
  have hN := Nat.mul_le_mul hn (show 17*A+2*(q+1)+6 ≤ 280*(b+q) by omega)
  have hAM := Nat.mul_le_mul_left 2189 hAQ
  have hRest : b+(k+1)+123 ≤ 16*(b+q) := by omega
  have hOther : n*(17*A+2*(q+1)+6)+2189*A+b+(k+1)+123 ≤ 131072*C*(b+q) := by
    nlinarith only [hN,hAM,hRest,hScale]
  have hHigh := Nat.mul_le_mul (show 121110528 ≤ 2097152*C by omega) (show q+1 ≤ b+q by omega)
  have hStep : short n (k+1) = q+1 := by dsimp [q,short]; omega
  rw [GeneralPaperEqualDrawAddressCapacity.profile_eq,hStep]
  have hWord : word n k b = 67108864*(b+q) := by unfold word GeneralPaperEqualBitDrawRates.size; dsimp [q,short]; omega
  rw [hWord]
  change 66060288*A*(q+1)+121110528*(q+1)+n*(17*A+2*(q+1)+6)+2189*A+b+(k+1)+123 ≤ C*(67108864*(b+q))
  nlinarith only [hCache,hOther,hHigh,Nat.zero_le (C*(b+q))]

theorem capacity (n m k b : ℕ) (hm : m ≤ 3) (hb : 3 ≤ b) :
    GeneralPaperEqualDrawAddressCapacity.profile (address n m k b) n (k+1) b < 2^address n m k b := by
  have h := profile_pool n m k b hm hb
  have hlt := lt_pow_binaryWordWidth ((n+m+k+69)*(word n k b+1)+1)
  exact h.trans_lt ((by nlinarith : (n+m+k+69)*word n k b < (n+m+k+69)*(word n k b+1)+1).trans hlt)

end Blotto.GeneralPaperEqualFirstDrawCapacity
