import Blotto.GeneralPaperMixedPrimitiveStorage

/-! Rational length extraction stores actual A-priced partial/parent fields
at physical width S, bounded by the existing S-priced lifetime. -/
namespace Blotto.GeneralPaperMixedRationalLengthStorage
open GeneralPaperEncodedScalarStorage (fields)
open GeneralPaperMixedPrimitiveStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def footprint (model : RationalCostModel) (S A : ℕ) (q : ℚ) : ℕ :=
  let num := GeneralPaperStoredWordLength.run A q.num.natAbs
  let den := GeneralPaperStoredWordLength.run A q.den
  let sum := GeneralPaperNaturalScalarStep.run model A .add num.1 den.1
  let result := GeneralPaperNaturalScalarStep.run model A .add sum.1 1
  let actual := GeneralPaperStoredRationalWordLength.run model A q
  rationalWordWidth q + wordFoot S A q.num.natAbs + wordFoot S A q.den +
    scalarFoot model S A num.1 den.1 sum.1 + scalarFoot model S A sum.1 1 result.1 +
    fields S [num.1, den.1, sum.1, result.1, num.2, den.2, sum.2, result.2, actual.2] + 256 * S

theorem diagonal (model : RationalCostModel) (S : ℕ) (q : ℚ) :
    footprint model S S q = GeneralPaperWordLengthLifetime.rationalFoot model S q := rfl

theorem le_diagonal (model : RationalCostModel) (S A : ℕ) (h : A ≤ S) (q : ℚ) :
    footprint model S A q ≤ footprint model S S q := by
  let num := binaryWordWidth q.num.natAbs
  let den := binaryWordWidth q.den
  have hn := word_price_mono S A q.num.natAbs h
  have hd := word_price_mono S A q.den h
  have hs := GeneralPaperMeasuredInitializerMonotonicity.scalar model A S h .add num den
  have hr := GeneralPaperMeasuredInitializerMonotonicity.scalar model A S h .add (num + den) 1
  have hp := GeneralPaperMeasuredInitializerMonotonicity.rational model A S h q
  have hc := fields_mono S
    [num, den, num + den, num + den + 1, (GeneralPaperStoredWordLength.run A q.num.natAbs).2,
      (GeneralPaperStoredWordLength.run A q.den).2, (GeneralPaperNaturalScalarStep.run model A .add num den).2,
      (GeneralPaperNaturalScalarStep.run model A .add (num + den) 1).2, (GeneralPaperStoredRationalWordLength.run model A q).2]
    [num, den, num + den, num + den + 1, (GeneralPaperStoredWordLength.run S q.num.natAbs).2,
      (GeneralPaperStoredWordLength.run S q.den).2, (GeneralPaperNaturalScalarStep.run model S .add num den).2,
      (GeneralPaperNaturalScalarStep.run model S .add (num + den) 1).2, (GeneralPaperStoredRationalWordLength.run model S q).2]
    (.cons le_rfl (.cons le_rfl (.cons le_rfl (.cons le_rfl
      (.cons hn (.cons hd (.cons hs (.cons hr (.cons hp .nil)))))))))
  have hNum := word_le_diagonal S A q.num.natAbs h
  have hDen := word_le_diagonal S A q.den h
  have hSum := scalar_le_diagonal model S A num den (num + den) h
  have hResult := scalar_le_diagonal model S A (num + den) 1 (num + den + 1) h
  simp only [footprint, GeneralPaperStoredWordLength.data, GeneralPaperNaturalScalarStep.data,
    GeneralPaperNaturalScalarStep.Op.apply]
  dsimp only [num, den] at *
  omega

theorem bounded (model : RationalCostModel) (S A : ℕ) (h : A ≤ S) (q : ℚ) :
    footprint model S A q ≤ rationalWordWidth q + 256 * (GeneralPaperStoredRationalWordLength.run model S q).2 :=
  (le_diagonal model S A h q).trans (by rw [diagonal]; exact GeneralPaperWordLengthLifetime.rational_bounded model S q)

theorem input_bound (model : RationalCostModel) (S A : ℕ) (h : A ≤ S) (q : ℚ) :
    footprint model S A q ≤ GeneralPaperWordLengthLifetime.rationalProfile model S (rationalWordWidth q) :=
  (le_diagonal model S A h q).trans (by rw [diagonal]; exact GeneralPaperWordLengthLifetime.rational_input_bound model S q)

end Blotto.GeneralPaperMixedRationalLengthStorage
