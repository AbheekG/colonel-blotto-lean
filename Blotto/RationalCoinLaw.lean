import Blotto.RationalCoinFailure
import Blotto.FairBitExpectation

/-! The actual outcome probabilities of the rational coin interpreter.
Completed true/false outcomes are subprobabilities of the exact Bernoulli
law; their entire missing mass is the exhausted-prefix event. -/

namespace Blotto
open MeasureTheory Set

noncomputable def coinOutcomeProbability (K : ℕ) (p : ℚ) (o : Option Bool) : ℝ :=
  (fairBitLaw K : Measure (Fin K → Bool)).real {bits | (runRationalCoin K p bits).1 = o}

def coinOutcomeIndicator (K : ℕ) (p : ℚ) (o : Option Bool) (bits : Fin K → Bool) : ℝ :=
  if (runRationalCoin K p bits).1 = o then 1 else 0

theorem coinOutcomeProbability_integral (K : ℕ) (p : ℚ) (o : Option Bool) :
    coinOutcomeProbability K p o =
      ∫ bits, coinOutcomeIndicator K p o bits ∂(fairBitLaw K : Measure (Fin K → Bool)) := by
  let A : Set (Fin K → Bool) := {bits | (runRationalCoin K p bits).1 = o}
  have hA : MeasurableSet A := A.to_countable.measurableSet
  have he : coinOutcomeIndicator K p o = A.indicator (fun _ => (1 : ℝ)) := by
    funext bits
    simp [coinOutcomeIndicator, A, Set.indicator_apply]
  rw [he, integral_indicator_const _ hA, smul_eq_mul, mul_one]
  rfl

theorem coinOutcomeProbability_step (K : ℕ) (p : ℚ) (o : Option Bool)
    (hp : ¬p ≤ 0) (hp1 : ¬1 ≤ p) :
    coinOutcomeProbability (K + 1) p o =
      (1 / 2 : ℝ) * coinOutcomeProbability K (coinResidual p) o +
        (1 / 2 : ℝ) * if some (probabilityDigit p) = o then 1 else 0 := by
  rw [coinOutcomeProbability_integral, fairBitLaw_integral_split]
  have hf : (fun bits : Fin K → Bool => coinOutcomeIndicator (K + 1) p o (prependBit (probabilityDigit p) bits)) =
      coinOutcomeIndicator K (coinResidual p) o := by
    funext bits
    simp [coinOutcomeIndicator, runRationalCoin, hp, hp1, prependBit]
  have hg : (fun bits : Fin K → Bool => coinOutcomeIndicator (K + 1) p o (prependBit (!(probabilityDigit p)) bits)) =
      fun _ => if some (probabilityDigit p) = o then (1 : ℝ) else 0 := by
    funext bits
    simp [coinOutcomeIndicator, runRationalCoin, hp, hp1, prependBit]
  cases hd : probabilityDigit p
  · have hf' := hf
    have hg' := hg
    rw [hd] at hf' hg'
    simp only [Bool.not_false] at hg'
    rw [hf', hg', integral_const, probReal_univ, one_smul, ← coinOutcomeProbability_integral]
  · have hf' := hf
    have hg' := hg
    rw [hd] at hf' hg'
    simp only [Bool.not_true] at hg'
    rw [hg', hf', integral_const, probReal_univ, one_smul, ← coinOutcomeProbability_integral]
    ring

theorem coinOutcomeProbability_partition (K : ℕ) (p : ℚ) :
    coinOutcomeProbability K p (some true) + coinOutcomeProbability K p (some false) + coinOutcomeProbability K p none = 1 := by
  have he : (fun bits : Fin K → Bool => coinOutcomeIndicator K p (some true) bits +
      coinOutcomeIndicator K p (some false) bits + coinOutcomeIndicator K p none bits) = fun _ => (1 : ℝ) := by
    funext bits
    cases ho : (runRationalCoin K p bits).1 with
    | none => simp [coinOutcomeIndicator, ho]
    | some b => cases b <;> simp [coinOutcomeIndicator, ho]
  rw [coinOutcomeProbability_integral, coinOutcomeProbability_integral, coinOutcomeProbability_integral,
    ← integral_add Integrable.of_finite Integrable.of_finite, ← integral_add Integrable.of_finite Integrable.of_finite,
    he, integral_const, probReal_univ, one_smul]

theorem coinOutcomeProbability_completed_le (K : ℕ) (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) :
    coinOutcomeProbability K p (some true) ≤ (p : ℝ) ∧ coinOutcomeProbability K p (some false) ≤ 1 - (p : ℝ) := by
  induction K generalizing p with
  | zero =>
    by_cases h0 : p ≤ 0
    · have he : p = 0 := le_antisymm h0 hp.1
      subst p
      simp [coinOutcomeProbability, runRationalCoin]
    by_cases h1 : 1 ≤ p
    · have he : p = 1 := le_antisymm hp.2 h1
      subst p
      norm_num [coinOutcomeProbability, runRationalCoin]
    · simp only [coinOutcomeProbability, runRationalCoin, h0, h1, ite_false]
      have hpR : (0 : ℝ) ≤ p ∧ (p : ℝ) ≤ 1 := by exact_mod_cast hp
      have hb : (0 : ℝ) ≤ p ∧ (0 : ℝ) ≤ 1 - (p : ℝ) := ⟨hpR.1, sub_nonneg.mpr hpR.2⟩
      simpa using hb
  | succ K ih =>
    by_cases h0 : p ≤ 0
    · have he : p = 0 := le_antisymm h0 hp.1
      subst p
      simp [coinOutcomeProbability, runRationalCoin]
    by_cases h1 : 1 ≤ p
    · have he : p = 1 := le_antisymm hp.2 h1
      subst p
      norm_num [coinOutcomeProbability, runRationalCoin]
    · have hr := ih (coinResidual p) (coinResidual_bounds hp)
      rw [coinOutcomeProbability_step K p (some true) h0 h1, coinOutcomeProbability_step K p (some false) h0 h1]
      cases hd : probabilityDigit p
      · have he : (coinResidual p : ℝ) = 2 * (p : ℝ) := by simp [coinResidual, hd]
        simp only [Option.some.injEq, Bool.false_eq_true, ite_false, ite_true, mul_zero, add_zero, mul_one]
        rw [he] at hr
        constructor <;> linarith [hr.1, hr.2]
      · have he : (coinResidual p : ℝ) = 2 * (p : ℝ) - 1 := by simp [coinResidual, hd]
        simp only [Option.some.injEq, Bool.true_eq_false, ite_false, ite_true, mul_zero, add_zero, mul_one]
        rw [he] at hr
        constructor <;> linarith [hr.1, hr.2]

theorem coinOutcomeProbability_true_error (K : ℕ) (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) :
    |coinOutcomeProbability K p (some true) - (p : ℝ)| ≤ 1 / (2 : ℝ) ^ K := by
  have he := coinOutcomeProbability_completed_le K p hp
  have hs := coinOutcomeProbability_partition K p
  have hf := runRationalCoin_failure_probability K p
  change coinOutcomeProbability K p none ≤ _ at hf
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Blotto
