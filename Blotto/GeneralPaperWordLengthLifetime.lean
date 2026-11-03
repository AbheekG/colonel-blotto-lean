import Blotto.GeneralPaperEqualBooleanCapacity

/-! Bit-model length extraction scans an existing stored integer word and
keeps the input, short length, scan price and cursor/control records. The
rational wrapper scans numerator/denominator additively; only their short
lengths enter natural scalar arithmetic. Original q is retained once here. -/
namespace Blotto.GeneralPaperWordLengthLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def footprint (A n : ℕ) : ℕ :=
  let actual := GeneralPaperStoredWordLength.run A n
  natBits n + natBits actual.1 + actual.2 + fields A [actual.1, actual.2] + 128 * A

theorem bounded (A n : ℕ) : footprint A n ≤ 32 * (GeneralPaperStoredWordLength.run A n).2 := by
  let F := (GeneralPaperStoredWordLength.run A n).2
  have hF : F = 32 * (binaryWordWidth n + binaryWordWidth (binaryWordWidth n) + A + 1) := rfl
  have hLength : natBits (GeneralPaperStoredWordLength.run A n).1 ≤ F := by
    change 1 + binaryWordWidth (binaryWordWidth n) ≤ _
    omega
  have hFields := GeneralPaperEncodedScalarStorage.fields_bound A (F + 2)
    [(GeneralPaperStoredWordLength.run A n).1, F] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · omega
      · exact GeneralPaperNaturalScalarLifetime.counter_word _)
  change fields A _ ≤ 2 * (F + 2 + A) + 32 * A at hFields
  change natBits n + natBits (GeneralPaperStoredWordLength.run A n).1 + F +
    fields A [(GeneralPaperStoredWordLength.run A n).1, F] + 128 * A ≤ 32 * F
  unfold natBits at *
  omega

def rationalFoot (model : RationalCostModel) (A : ℕ) (q : ℚ) : ℕ :=
  let num := GeneralPaperStoredWordLength.run A q.num.natAbs
  let den := GeneralPaperStoredWordLength.run A q.den
  let sum := GeneralPaperNaturalScalarStep.run model A .add num.1 den.1
  let result := GeneralPaperNaturalScalarStep.run model A .add sum.1 1
  let actual := GeneralPaperStoredRationalWordLength.run model A q
  rationalWordWidth q + footprint A q.num.natAbs + footprint A q.den +
    GeneralPaperNaturalScalarLifetime.footprint model A .add num.1 den.1 +
    GeneralPaperNaturalScalarLifetime.footprint model A .add sum.1 1 +
    fields A [num.1, den.1, sum.1, result.1, num.2, den.2, sum.2, result.2, actual.2] + 256 * A

theorem rational_bounded (model : RationalCostModel) (A : ℕ) (q : ℚ) :
    rationalFoot model A q ≤ rationalWordWidth q + 256 * (GeneralPaperStoredRationalWordLength.run model A q).2 := by
  let num := GeneralPaperStoredWordLength.run A q.num.natAbs
  let den := GeneralPaperStoredWordLength.run A q.den
  let sum := GeneralPaperNaturalScalarStep.run model A .add num.1 den.1
  let result := GeneralPaperNaturalScalarStep.run model A .add sum.1 1
  let F := (GeneralPaperStoredRationalWordLength.run model A q).2
  have hF : F = num.2 + den.2 + sum.2 + result.2 + 64 * A + 64 := rfl
  have hNum := bounded A q.num.natAbs
  change footprint A q.num.natAbs ≤ 32 * num.2 at hNum
  have hDen := bounded A q.den
  change footprint A q.den ≤ 32 * den.2 at hDen
  have hSum := GeneralPaperNaturalScalarLifetime.bounded model A .add num.1 den.1
  change GeneralPaperNaturalScalarLifetime.footprint model A .add num.1 den.1 ≤ 32 * sum.2 at hSum
  have hResult := GeneralPaperNaturalScalarLifetime.bounded model A .add sum.1 1
  change GeneralPaperNaturalScalarLifetime.footprint model A .add sum.1 1 ≤ 32 * result.2 at hResult
  have hNumWord : natBits num.1 ≤ num.2 := by
    change 1 + binaryWordWidth (binaryWordWidth q.num.natAbs) ≤ _
    dsimp only [num, GeneralPaperStoredWordLength.run]
    omega
  have hDenWord : natBits den.1 ≤ den.2 := by
    change 1 + binaryWordWidth (binaryWordWidth q.den) ≤ _
    dsimp only [den, GeneralPaperStoredWordLength.run]
    omega
  have hSumWord := GeneralPaperNaturalScalarLifetime.written model A .add num.1 den.1
  change natBits sum.1 ≤ sum.2 at hSumWord
  have hResultWord := GeneralPaperNaturalScalarLifetime.written model A .add sum.1 1
  change natBits result.1 ≤ result.2 at hResultWord
  have hFields := GeneralPaperEncodedScalarStorage.fields_bound A (F + 2)
    [num.1, den.1, sum.1, result.1, num.2, den.2, sum.2, result.2, F] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega)
      · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega)
      · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega)
      · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega)
      · exact GeneralPaperNaturalScalarLifetime.counter_word _)
  change fields A _ ≤ 9 * (F + 2 + A) + 32 * A at hFields
  change rationalWordWidth q + footprint A q.num.natAbs + footprint A q.den +
    GeneralPaperNaturalScalarLifetime.footprint model A .add num.1 den.1 +
    GeneralPaperNaturalScalarLifetime.footprint model A .add sum.1 1 +
    fields A [num.1, den.1, sum.1, result.1, num.2, den.2, sum.2, result.2, F] + 256 * A ≤ rationalWordWidth q + 256 * F
  omega

def rationalProfile (model : RationalCostModel) (A b : ℕ) : ℕ :=
  b + 262144 * (b + A + model.rat (binaryWordWidth b + 3) + 1)

theorem rational_input_bound (model : RationalCostModel) (A : ℕ) (q : ℚ) :
    rationalFoot model A q ≤ rationalProfile model A (rationalWordWidth q) :=
  (rational_bounded model A q).trans ((Nat.add_le_add_left
    (Nat.mul_le_mul_left 256 (GeneralPaperStoredRationalWordLength.work model A q)) _).trans_eq (by unfold rationalProfile; ring))

end Blotto.GeneralPaperWordLengthLifetime
