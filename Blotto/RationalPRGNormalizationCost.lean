import Blotto.RationalPRGOriginalProcessing
import Blotto.RationalExpressionValue

/-! Normalizing ordered positive budgets uses one guarded division. This
formula and stored result are priced against original input words. Decoding,
promise recognition and record/index management are separate operations. -/

namespace Blotto.RationalPRGOriginalInput

def normalizationExpression : RationalExpression 2 := .div (.input 0) (.input 1)

def normalizationEnvironment {n : ℕ} (i : RationalPRGOriginalInput n) : FixedArrayTable 2 ℚ :=
  FixedArrayTable.ofFn ![i.b, i.a]

theorem normalizationExpression_value {n : ℕ} (i : RationalPRGOriginalInput n) :
    normalizationExpression.value i.normalizationEnvironment = i.normalizedInput.b := by
  simp [normalizationExpression, normalizationEnvironment, FixedArrayTable.read_ofFn, normalizedInput]

def normalizationBitWork {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) : ℕ :=
  normalizationExpression.bitCost model i.normalizationEnvironment + rationalWordWidth i.normalizedInput.b

theorem normalizationBitWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) :
    i.normalizationBitWork model ≤ 5 * model.rat (1 + 2 * i.originalInputWordWidth) := by
  have hA : RationalHeight i.a i.originalInputWordWidth :=
    (rationalHeight_of_wordWidth i.a).mono (by unfold originalInputWordWidth; omega)
  have hB : RationalHeight i.b i.originalInputWordWidth :=
    (rationalHeight_of_wordWidth i.b).mono (by unfold originalInputWordWidth; omega)
  have hEnv : normalizationExpression.AllRunHeights i.normalizationEnvironment i.originalInputWordWidth := by
    simpa [normalizationExpression, normalizationEnvironment, FixedArrayTable.read_ofFn,
      RationalExpression.AllRunHeights, RationalExpression.run] using And.intro hB (And.intro hA (And.intro hB hA))
  have hCode := normalizationExpression.bitCost_bound model i.normalizationEnvironment _ hEnv
  have hOps : normalizationExpression.operationBound = 4 := rfl
  rw [hOps] at hCode
  have hRatio := rationalWordWidth_of_height ((rationalHeight_of_wordWidth i.b).div (rationalHeight_of_wordWidth i.a))
  change rationalWordWidth i.normalizedInput.b ≤ 1 + 2 * (rationalWordWidth i.b + rationalWordWidth i.a) at hRatio
  have hw : 1 + 2 * (rationalWordWidth i.b + rationalWordWidth i.a) ≤ 1 + 2 * i.originalInputWordWidth := by
    unfold originalInputWordWidth
    omega
  have hOut := (hRatio.trans hw).trans (model.word_le _)
  unfold normalizationBitWork
  omega

end Blotto.RationalPRGOriginalInput
