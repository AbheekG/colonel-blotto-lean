import Blotto.RationalPRGNormalizationCost
import Blotto.RealExpression

/-! Exact-real normalization and output scaling use the same division and
multiplication formulas as the rational path. These are real-RAM operation
labels; they do not provide floating-point execution or allocator bounds. -/

namespace Blotto.RealPRGNormalizationScaling

noncomputable def normalizationEnvironment (a b : ℝ) : FixedArrayTable 2 ℝ :=
  FixedArrayTable.ofFn ![b, a]

theorem normalization_value (a b : ℝ) :
    RationalPRGOriginalInput.normalizationExpression.realValue (normalizationEnvironment a b) = b / a := by
  simp [RationalPRGOriginalInput.normalizationExpression, normalizationEnvironment, FixedArrayTable.read_ofFn]

theorem normalization_operations (a b : ℝ) :
    (RationalPRGOriginalInput.normalizationExpression.runReal (normalizationEnvironment a b)).2 = 4 := rfl

def scaleExpression : RationalExpression 2 := .mul (.input 0) (.input 1)

noncomputable def scaleEnvironment (a x : ℝ) : FixedArrayTable 2 ℝ := FixedArrayTable.ofFn ![a, x]

theorem scale_value (a x : ℝ) : scaleExpression.realValue (scaleEnvironment a x) = a * x := by
  simp [scaleExpression, scaleEnvironment, FixedArrayTable.read_ofFn]

theorem scale_operations (a x : ℝ) : (scaleExpression.runReal (scaleEnvironment a x)).2 = 3 := rfl

noncomputable def rowOperationWork {n : ℕ} (a : ℝ) (row : Fin n → ℝ) : ℕ :=
  ∑ j, ((scaleExpression.runReal (scaleEnvironment a (row j))).2 + 1)

theorem rowOperationWork_eq {n : ℕ} (a : ℝ) (row : Fin n → ℝ) : rowOperationWork a row = 4 * n := by
  simp only [rowOperationWork, scale_operations]
  simp
  omega

end Blotto.RealPRGNormalizationScaling
