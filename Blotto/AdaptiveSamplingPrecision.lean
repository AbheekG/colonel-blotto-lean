import Blotto.RationalEpsilonRejection
import Blotto.RationalRejectionSchedule

/-! Native rational per-draw accuracy and dyadic field precision control total
adaptive run error. The call count is explicit; a global bit/word/work cap for
those calls remains a distinct resource obligation. -/

namespace Blotto

def adaptiveDrawTolerance (accuracy : ℚ) (calls : ℕ) : ℚ := accuracy / (4 * ((calls : ℚ) + 1))

theorem adaptiveDrawTolerance_positive (accuracy : ℚ) (ha : 0 < accuracy) (calls : ℕ) :
    0 < adaptiveDrawTolerance accuracy calls := by unfold adaptiveDrawTolerance; positivity

def adaptiveFieldPrecision (accuracy : ℚ) (calls : ℕ) : ℕ :=
  RationalWeightedGuideTree.epsilonPrecision (adaptiveDrawTolerance accuracy calls)

theorem adaptiveFieldPrecision_error (accuracy : ℚ) (ha : 0 < accuracy) (calls : ℕ) :
    1 / (2 : ℝ) ^ adaptiveFieldPrecision accuracy calls ≤ (adaptiveDrawTolerance accuracy calls : ℝ) :=
  RationalWeightedGuideTree.epsilonPrecision_guard _ (adaptiveDrawTolerance_positive accuracy ha calls)

theorem adaptiveTotalDrawError (accuracy : ℚ) (ha : 0 < accuracy) (calls : ℕ) :
    (calls : ℝ) * (2 * (adaptiveDrawTolerance accuracy calls : ℝ) +
      1 / (2 : ℝ) ^ adaptiveFieldPrecision accuracy calls) ≤ (accuracy : ℝ) := by
  have hf := adaptiveFieldPrecision_error accuracy ha calls
  have hT : (0 : ℝ) ≤ calls := by positivity
  have hA : (0 : ℝ) ≤ (accuracy : ℝ) := by exact_mod_cast ha.le
  have hTol : (adaptiveDrawTolerance accuracy calls : ℝ) =
      (accuracy : ℝ) / (4 * ((calls : ℝ) + 1)) := by simp [adaptiveDrawTolerance]
  have hmul := mul_le_mul_of_nonneg_left hf hT
  rw [hTol] at hmul ⊢
  have hScale : (calls : ℝ) * (3 * ((accuracy : ℝ) / (4 * ((calls : ℝ) + 1)))) ≤ (accuracy : ℝ) := by
    calc
      _ = (3 * (calls : ℝ) * (accuracy : ℝ)) / (4 * ((calls : ℝ) + 1)) := by ring
      _ ≤ (accuracy : ℝ) := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((calls : ℝ) + 1))).mpr (by nlinarith)
  nlinarith

end Blotto
