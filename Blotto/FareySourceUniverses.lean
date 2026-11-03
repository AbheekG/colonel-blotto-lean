import Blotto.FareyRankUniverse

/-! The exact R127 source parameters give native candidate/response rank
universes with all decoder premises proved. D=q(m+2)^[m(K0-1)+1] and
Q=2mqD^(m+2); the response shift is 1/Q. Word bounds count this actual
representation. Short-ratio compilation and complete execution cost are separate. -/

namespace Blotto.Farey

def sourceExponent (m K0 : ℕ) : ℕ := m * (K0 - 1) + 1
def sourceOrder (q m K0 : ℕ) : ℕ := q * (m + 2) ^ sourceExponent m K0
def sourceShiftDenominator (D m q : ℕ) : ℕ := 2 * m * q * D ^ (m + 2)

theorem sourceOrder_positive (q m K0 : ℕ) (hq : 0 < q) : 0 < sourceOrder q m K0 := by
  unfold sourceOrder
  positivity

theorem sourceShiftDenominator_large (D m q : ℕ) (hD : 0 < D) (hm : 0 < m) (hq : 0 < q) :
    D * D < sourceShiftDenominator D m q := by
  have hp : D ^ 2 ≤ D ^ (m + 2) := pow_le_pow_right₀ (by omega : 1 ≤ D) (by omega)
  have hf : 2 ≤ 2 * m * q := by nlinarith
  have hz : 0 < D * D := Nat.mul_pos hD hD
  unfold sourceShiftDenominator
  rw [pow_two] at hp
  nlinarith

def candidateUniverse (D : ℕ) (hD : 0 < D) : RankUniverse where
  order := D
  order_positive := hD
  shift := 0
  shift_nonnegative := le_refl _
  shift_small := by positivity

def responseUniverse (D m q : ℕ) (hD : 0 < D) (hm : 0 < m) (hq : 0 < q) : RankUniverse where
  order := D
  order_positive := hD
  shift := 1 / (sourceShiftDenominator D m q : ℚ)
  shift_nonnegative := by unfold sourceShiftDenominator; positivity
  shift_small := by
    have hp : (0 : ℚ) < (D : ℚ) * D := by positivity
    have hLarge : (D : ℚ) * D < sourceShiftDenominator D m q := by
      exact_mod_cast sourceShiftDenominator_large D m q hD hm hq
    exact one_div_lt_one_div_of_lt hp hLarge

def sourceCandidateUniverse (q m K0 : ℕ) (hq : 0 < q) : RankUniverse :=
  candidateUniverse (sourceOrder q m K0) (sourceOrder_positive q m K0 hq)

def sourceResponseUniverse (q m K0 : ℕ) (hq : 0 < q) (hm : 0 < m) : RankUniverse :=
  responseUniverse (sourceOrder q m K0) m q (sourceOrder_positive q m K0 hq) hm hq

theorem binaryWordWidth_power (D n : ℕ) : binaryWordWidth (D ^ n) ≤ 1 + n * binaryWordWidth D := by
  induction n with
  | zero => simpa only [pow_zero, zero_mul, add_zero] using (show binaryWordWidth 1 ≤ 1 by decide)
  | succ n ih =>
    rw [pow_succ]
    have hp := binaryWordWidth_mul (D ^ n) D
    nlinarith

theorem sourceOrder_word_bound (q m K0 : ℕ) :
    binaryWordWidth (sourceOrder q m K0) ≤ binaryWordWidth q + 1 + sourceExponent m K0 * binaryWordWidth (m + 2) := by
  have hp := binaryWordWidth_mul q ((m + 2) ^ sourceExponent m K0)
  have he := binaryWordWidth_power (m + 2) (sourceExponent m K0)
  unfold sourceOrder
  omega

theorem sourceCode_word_bound (q m K0 : ℕ) (hq : 0 < q) :
    binaryWordWidth (rankCap (sourceOrder q m K0) + 1) ≤
      8 + 2 * binaryWordWidth q + 2 * sourceExponent m K0 * binaryWordWidth (m + 2) := by
  have hc := rankCap_word_bound (sourceOrder q m K0) (sourceOrder_positive q m K0 hq)
  have ho := sourceOrder_word_bound q m K0
  nlinarith

theorem response_shift_positive (D m q : ℕ) (hD : 0 < D) (hm : 0 < m) (hq : 0 < q) :
    0 < (responseUniverse D m q hD hm hq).shift := by
  unfold responseUniverse sourceShiftDenominator
  positivity

end Blotto.Farey
