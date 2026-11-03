import Blotto.BinaryRatioPrecision
import Blotto.RationalPRGOriginalSampler

/-! Accuracy is accepted as two positive integer words, without reducing
its fraction. Runtime precision uses bit lengths and one shift comparison;
the real quotient is used only in the error theorem. Binary framing is separate. -/

namespace Blotto

structure BinaryAccuracyInput where
  numerator : ℕ
  denominator : ℕ
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator

namespace BinaryAccuracyInput

noncomputable def real (a : BinaryAccuracyInput) : ℝ := (a.numerator : ℝ) / a.denominator

def precision (a : BinaryAccuracyInput) : ℕ := binaryRatioPrecision (32 * a.denominator) a.numerator

theorem real_pos (a : BinaryAccuracyInput) : 0 < a.real :=
  div_pos (by exact_mod_cast a.numerator_pos) (by exact_mod_cast a.denominator_pos)

theorem precision_guard (a : BinaryAccuracyInput) : 32 ≤ a.real * (2 : ℝ) ^ a.precision := by
  have hn := binaryRatioPrecision_bound (32 * a.denominator) a.numerator a.numerator_pos
  have hR : (32 : ℝ) * a.denominator ≤ (a.numerator : ℝ) * (2 : ℝ) ^ a.precision := by exact_mod_cast hn
  have hd : (0 : ℝ) < a.denominator := by exact_mod_cast a.denominator_pos
  apply (mul_le_mul_iff_of_pos_right hd).mp
  unfold real
  convert! hR using 1; field_simp

theorem original_regrets {n : ℕ} (a : BinaryAccuracyInput) (i : RationalPRGOriginalInput n) :
    regret i.realValues (i.a : ℝ) (i.richSampleLaw a.precision) (i.poorSampleLaw a.precision) < a.real ∧
      regret i.realValues (i.b : ℝ) (i.poorSampleLaw a.precision) (i.richSampleLaw a.precision) < a.real := by
  have h := i.sample_regrets a.precision
  have he := prg_precision_error a.real_pos a.precision_guard
  have hsum : 2 * (5 / (2 * (2 : ℝ) ^ a.precision)) = 5 / (2 : ℝ) ^ a.precision := by field_simp
  rw [hsum] at he
  constructor <;> linarith [h.1, h.2]

end BinaryAccuracyInput
end Blotto
