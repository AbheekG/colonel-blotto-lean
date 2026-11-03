import Blotto.RationalRejectionNativeContract

/-! A block of factor-majorant trials reduces geometric failure by at least
one half. Repeating dyadic precision blocks supplies a logarithmic-accuracy
attempt schedule without an uncharged numerical-tail search. -/

namespace Blotto

theorem reciprocal_geometric_bound (p : ℝ) (_hp : 0 ≤ p) (h1 : p ≤ 1) (n : ℕ) :
    (1 + (n : ℝ) * p) * (1 - p) ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    have hq : 0 ≤ (1 - p) ^ n := pow_nonneg (by linarith) _
    have hstep : (1 + ((n : ℝ) + 1) * p) * (1 - p) ≤ 1 + (n : ℝ) * p := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have he : (1 + ((n : ℝ) + 1) * p) * (1 - p) =
          1 + (n : ℝ) * p - ((n : ℝ) + 1) * p ^ 2 := by ring
      rw [he]
      have hTerm : 0 ≤ ((n : ℝ) + 1) * p ^ 2 := mul_nonneg (by linarith) (sq_nonneg p)
      linarith
    calc
      _ = ((1 + ((n : ℝ) + 1) * p) * (1 - p)) * (1 - p) ^ n := by ring
      _ ≤ (1 + (n : ℝ) * p) * (1 - p) ^ n := mul_le_mul_of_nonneg_right hstep hq
      _ ≤ 1 := ih

theorem geometric_factor_block {factor : ℝ} (hf : 1 ≤ factor) (block : ℕ)
    (hb : factor ≤ (block : ℝ)) : (1 - 1 / factor) ^ block ≤ (1 / 2 : ℝ) := by
  have hf0 : 0 < factor := by linarith
  have hp0 : 0 ≤ 1 / factor := by positivity
  have hp1 : 1 / factor ≤ 1 := (div_le_one hf0).mpr hf
  have he := reciprocal_geometric_bound (1 / factor) hp0 hp1 block
  have hbp : 1 ≤ (block : ℝ) * (1 / factor) := by
    rw [mul_one_div]
    exact (one_le_div hf0).mpr hb
  have hq : 0 ≤ (1 - 1 / factor) ^ block := pow_nonneg (by linarith) _
  nlinarith

theorem geometric_factor_blocks {factor : ℝ} (hf : 1 ≤ factor) (block precision : ℕ)
    (hb : factor ≤ (block : ℝ)) :
    (1 - 1 / factor) ^ (block * precision) ≤ 1 / (2 : ℝ) ^ precision := by
  rw [pow_mul]
  have hq : 0 ≤ (1 - 1 / factor) ^ block := pow_nonneg (by have hp := (div_le_one (show 0 < factor by linarith)).mpr hf; linarith) _
  have he := pow_le_pow_left₀ hq (geometric_factor_block hf block hb) precision
  simpa only [one_div_pow] using he

end Blotto
