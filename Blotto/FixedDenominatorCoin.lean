import Blotto.RationalCoinLaw
import Blotto.RationalCoinMoment

/-! Binary implementation of rational-coin comparison with a fixed positive
denominator. Each digit doubles the numerator, compares with the denominator,
and optionally subtracts it; no fraction reduction is performed in the loop.
The output and consumed-bit count refine the rational interpreter exactly. -/

namespace Blotto
open MeasureTheory Set

def denominatorDigit (a b : ℕ) : Bool := decide (b ≤ 2 * a)
def numeratorResidual (a b : ℕ) : ℕ := 2 * a - if denominatorDigit a b then b else 0

def runFixedDenominatorCoin : (K : ℕ) → ℕ → ℕ → (Fin K → Bool) → Option Bool × ℕ
  | 0, a, b, _ => if a = 0 then (some false, 0) else if b ≤ a then (some true, 0) else (none, 0)
  | K + 1, a, b, bits =>
    if a = 0 then (some false, 0) else if b ≤ a then (some true, 0) else
      if bits 0 = denominatorDigit a b then
        let result := runFixedDenominatorCoin K (numeratorResidual a b) b (Fin.tail bits)
        (result.1, result.2 + 1)
      else (some (!bits 0), 1)

theorem probabilityDigit_ratio (a b : ℕ) (hb : 0 < b) :
    probabilityDigit ((a : ℚ) / b) = denominatorDigit a b := by
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have he : (1 / 2 : ℚ) ≤ (a : ℚ) / b ↔ b ≤ 2 * a := by
    rw [le_div_iff₀ hbQ]
    have he' : (1 / 2 : ℚ) * b ≤ a ↔ (b : ℚ) ≤ 2 * a := by constructor <;> intro h <;> linarith
    rw [he']
    norm_cast
  unfold probabilityDigit denominatorDigit
  simp only [he]

theorem coinResidual_ratio (a b : ℕ) (hb : 0 < b) :
    coinResidual ((a : ℚ) / b) = (numeratorResidual a b : ℚ) / b := by
  rw [coinResidual, probabilityDigit_ratio a b hb]
  unfold numeratorResidual
  by_cases hd : b ≤ 2 * a
  · have hd' : denominatorDigit a b = true := by simp [denominatorDigit, hd]
    rw [hd']
    change 2 * ((a : ℚ) / b) - 1 = ((2 * a - b : ℕ) : ℚ) / b
    rw [Nat.cast_sub hd, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  · have hd' : denominatorDigit a b = false := by simp [denominatorDigit, hd]
    rw [hd']
    change 2 * ((a : ℚ) / b) - 0 = ((2 * a - 0 : ℕ) : ℚ) / b
    rw [Nat.sub_zero, Nat.cast_mul, Nat.cast_ofNat]
    ring

theorem numeratorResidual_bounds (a b : ℕ) (hab : a ≤ b) : numeratorResidual a b ≤ b := by
  unfold numeratorResidual denominatorDigit
  split_ifs with hd
  · simp only [decide_eq_true_eq] at hd
    omega
  · simp only [decide_eq_true_eq] at hd
    omega

theorem runFixedDenominatorCoin_refines (K a b : ℕ) (hb : 0 < b) (bits : Fin K → Bool) :
    runFixedDenominatorCoin K a b bits = runRationalCoin K ((a : ℚ) / b) bits := by
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have h0 (a : ℕ) : ((a : ℚ) / b ≤ 0) ↔ a = 0 := by
    rw [div_le_iff₀ hbQ, zero_mul]
    exact_mod_cast (Nat.le_zero : a ≤ 0 ↔ a = 0)
  have h1 (a : ℕ) : ((1 : ℚ) ≤ (a : ℚ) / b) ↔ b ≤ a := by
    rw [le_div_iff₀ hbQ, one_mul]
    norm_cast
  induction K generalizing a with
  | zero => simp only [runFixedDenominatorCoin, runRationalCoin, h0 a, h1 a]
  | succ K ih =>
    simp only [runFixedDenominatorCoin, runRationalCoin, h0 a, h1 a, probabilityDigit_ratio a b hb]
    split_ifs
    · rfl
    · rfl
    · rw [ih, coinResidual_ratio a b hb]
    · rfl

theorem runFixedDenominatorCoin_bits_le (K a b : ℕ) (hb : 0 < b) (bits : Fin K → Bool) :
    (runFixedDenominatorCoin K a b bits).2 ≤ K := by
  rw [runFixedDenominatorCoin_refines K a b hb]
  exact runRationalCoin_bits_le _ _ _

theorem runFixedDenominatorCoin_failure_probability (K a b : ℕ) (hb : 0 < b) :
    (fairBitLaw K : Measure (Fin K → Bool)).real {bits | (runFixedDenominatorCoin K a b bits).1 = none} ≤ 1 / (2 : ℝ) ^ K := by
  have he : {bits : Fin K → Bool | (runFixedDenominatorCoin K a b bits).1 = none} =
      {bits | (runRationalCoin K ((a : ℚ) / b) bits).1 = none} := by
    ext bits
    change (runFixedDenominatorCoin K a b bits).1 = none ↔ (runRationalCoin K ((a : ℚ) / b) bits).1 = none
    rw [runFixedDenominatorCoin_refines K a b hb]
  rw [he]
  exact runRationalCoin_failure_probability _ _

theorem runFixedDenominatorCoin_moment (K a b : ℕ) (hb : 0 < b) :
    (∫ bits, (4 / 3 : ℝ) ^ (runFixedDenominatorCoin K a b bits).2 ∂(fairBitLaw K : Measure (Fin K → Bool))) ≤ 2 := by
  simp_rw [runFixedDenominatorCoin_refines K a b hb]
  exact runRationalCoin_moment _ _

theorem runFixedDenominatorCoin_true_error (K a b : ℕ) (hb : 0 < b) (hab : a ≤ b) :
    |(fairBitLaw K : Measure (Fin K → Bool)).real {bits | (runFixedDenominatorCoin K a b bits).1 = some true} -
      ((a : ℝ) / b)| ≤ 1 / (2 : ℝ) ^ K := by
  have hp : (0 : ℚ) ≤ (a : ℚ) / b ∧ (a : ℚ) / b ≤ 1 := by
    have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
    exact ⟨by positivity, (div_le_one hbQ).mpr (by exact_mod_cast hab)⟩
  have he := coinOutcomeProbability_true_error K ((a : ℚ) / b) hp
  unfold coinOutcomeProbability at he
  simp_rw [← runFixedDenominatorCoin_refines K a b hb] at he
  simpa only [Rat.cast_div, Rat.cast_natCast] using he

end Blotto
