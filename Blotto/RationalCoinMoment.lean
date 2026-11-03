import Blotto.RationalCoin
import Blotto.FairBitExpectation

/-! The actual consumed-bit count of a bounded rational coin has exponential
moment at most two, uniformly in its probability and available bit budget.
This is the one-step estimate for the adaptive shared-cap argument. -/

namespace Blotto
open MeasureTheory

theorem runRationalCoin_moment (K : ℕ) (p : ℚ) :
    (∫ bits, (4 / 3 : ℝ) ^ (runRationalCoin K p bits).2 ∂(fairBitLaw K : Measure (Fin K → Bool))) ≤ 2 := by
  induction K generalizing p with
  | zero =>
    have he : (fun bits : Fin 0 → Bool => (4 / 3 : ℝ) ^ (runRationalCoin 0 p bits).2) = fun _ => (1 : ℝ) := by
      funext bits
      unfold runRationalCoin
      split_ifs <;> simp
    rw [he, integral_const, probReal_univ, one_smul]
    norm_num
  | succ K ih =>
    by_cases hp : p ≤ 0
    · simp [runRationalCoin, hp]
    by_cases hp1 : 1 ≤ p
    · simp [runRationalCoin, hp, hp1]
    rw [fairBitLaw_integral_split]
    have hf : (fun bits : Fin K → Bool => (4 / 3 : ℝ) ^
        (runRationalCoin (K + 1) p (prependBit (probabilityDigit p) bits)).2) =
        fun bits => (4 / 3 : ℝ) * (4 / 3 : ℝ) ^ (runRationalCoin K (coinResidual p) bits).2 := by
      funext bits
      simp only [runRationalCoin, hp, hp1, ite_false, prependBit, Fin.cons_zero, ite_true, Fin.tail_cons, pow_succ]
      ring
    have hg : (fun bits : Fin K → Bool => (4 / 3 : ℝ) ^
        (runRationalCoin (K + 1) p (prependBit (!(probabilityDigit p)) bits)).2) = fun _ => (4 / 3 : ℝ) := by
      funext bits
      simp [runRationalCoin, hp, hp1, prependBit]
    have he := ih (coinResidual p)
    cases hd : probabilityDigit p
    · have hf' := hf
      have hg' := hg
      rw [hd] at hf' hg'
      simp only [Bool.not_false] at hg'
      rw [hf', hg', integral_const_mul, integral_const, probReal_univ, one_smul]
      linarith
    · have hf' := hf
      have hg' := hg
      rw [hd] at hf' hg'
      simp only [Bool.not_true] at hg'
      rw [hg', hf', integral_const_mul, integral_const, probReal_univ, one_smul]
      linarith

end Blotto
