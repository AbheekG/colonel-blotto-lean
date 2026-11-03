import Blotto.GeneralPaperStoredWordLength

/-! Measure an original rational's canonical word length once. Numerator
and denominator scans are additive in the actual input encoding size;
only the short returned lengths enter the two scalar additions. -/
namespace Blotto.GeneralPaperStoredRationalWordLength
set_option autoImplicit false
set_option maxHeartbeats 1400000

def run (model : RationalCostModel) (A : ℕ) (q : ℚ) : ℕ × ℕ :=
  let num := GeneralPaperStoredWordLength.run A q.num.natAbs
  let den := GeneralPaperStoredWordLength.run A q.den
  let sum := GeneralPaperNaturalScalarStep.run model A .add num.1 den.1
  let result := GeneralPaperNaturalScalarStep.run model A .add sum.1 1
  (result.1, num.2 + den.2 + sum.2 + result.2 + 64 * A + 64)

theorem data (model : RationalCostModel) (A : ℕ) (q : ℚ) :
    (run model A q).1 = rationalWordWidth q := by
  unfold run GeneralPaperNaturalScalarStep.run GeneralPaperNaturalScalarStep.Op.apply
    GeneralPaperStoredWordLength.run rationalWordWidth
  dsimp only
  omega

theorem work (model : RationalCostModel) (A : ℕ) (q : ℚ) :
    (run model A q).2 ≤ 1024 * (rationalWordWidth q + A + model.rat (binaryWordWidth (rationalWordWidth q) + 3) + 1) := by
  let b := rationalWordWidth q
  let num := binaryWordWidth q.num.natAbs
  let den := binaryWordWidth q.den
  have hNum : num ≤ b := by dsimp [num, b, rationalWordWidth]; omega
  have hDen : den ≤ b := by dsimp [den, b, rationalWordWidth]; omega
  have hSum : num + den ≤ b := by dsimp [num, den, b, rationalWordWidth]; omega
  have hResult : num + den + 1 = b := by dsimp [num, den, b, rationalWordWidth]; omega
  have h1 : binaryWordWidth 1 = 1 := by decide
  have hNumW := binaryWordWidth_mono hNum
  have hDenW := binaryWordWidth_mono hDen
  have hSumW := binaryWordWidth_mono hSum
  have hPositive := binaryWordWidth_pos b
  have hAdd := GeneralPaperNaturalScalarStep.work model A .add num den (binaryWordWidth b + 3)
    (by unfold GeneralPaperNaturalScalarStep.word; omega)
    (by unfold GeneralPaperNaturalScalarStep.word; omega)
    (by change 1 + binaryWordWidth (num + den) ≤ binaryWordWidth b + 3; omega)
  have hFinal := GeneralPaperNaturalScalarStep.work model A .add (num + den) 1 (binaryWordWidth b + 3)
    (by unfold GeneralPaperNaturalScalarStep.word; omega)
    (by unfold GeneralPaperNaturalScalarStep.word; omega)
    (by change 1 + binaryWordWidth (num + den + 1) ≤ binaryWordWidth b + 3; rw [hResult]; omega)
  have hN := GeneralPaperStoredWordLength.work A q.num.natAbs
  have hD := GeneralPaperStoredWordLength.work A q.den
  change (GeneralPaperStoredWordLength.run A q.num.natAbs).2 ≤ 64 * (num + A + 1) at hN
  change (GeneralPaperStoredWordLength.run A q.den).2 ≤ 64 * (den + A + 1) at hD
  change (GeneralPaperStoredWordLength.run A q.num.natAbs).2 +
    (GeneralPaperStoredWordLength.run A q.den).2 +
    (GeneralPaperNaturalScalarStep.run model A .add num den).2 +
    (GeneralPaperNaturalScalarStep.run model A .add (num + den) 1).2 + 64 * A + 64 ≤
      1024 * (b + A + model.rat (binaryWordWidth b + 3) + 1)
  omega

end Blotto.GeneralPaperStoredRationalWordLength
