import Blotto.RationalExpressionWordWidth
import Blotto.BitIndex

/-! Canonical midpoint output uses at most K+2 bits in each unsigned word,
including the denominator's extra endpoint bit. -/

namespace Blotto

theorem dyadicMidpointSample_height (K : ℕ) (bits : Fin K → Bool) :
    RationalHeight (dyadicMidpointSample K bits) (K + 2) := by
  let n := 2 * (bitIndex K bits).val + 1
  have hN : n < 2 ^ (K + 2) := by
    have h := (dyadicMidpointSample_numerator K bits).2
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show K + 1 ≤ K + 2 by omega)
    exact h.trans_le hp
  have hd : 2 ^ (K + 1) < (2 : ℕ) ^ (K + 2) := by
    have hp := Nat.two_pow_pos (K + 1)
    rw [show K + 2 = (K + 1) + 1 by omega, pow_succ]
    omega
  have h := RationalHeight.fraction (n : ℤ) (2 ^ (K + 1)) (K + 2) (Nat.two_pow_pos _) (by simpa using hN) hd
  convert! h using 1
  simp [dyadicMidpointSample_refines, dyadicMidpointSampleReference, n, Nat.cast_add, Nat.cast_mul, mul_comm]

theorem dyadicMidpointSample_wordWidth (K : ℕ) (bits : Fin K → Bool) :
    rationalWordWidth (dyadicMidpointSample K bits) ≤ 1 + 2 * (K + 2) :=
  rationalWordWidth_of_height (dyadicMidpointSample_height K bits)

end Blotto
