import Blotto.GeneralPaperMixedAccuracyCountStorage

/-! Actual accuracy preparation charged at A, with every retained field
and Boolean/counter frame stored at physical reference S. -/
namespace Blotto.GeneralPaperMixedBinaryAccuracyStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperBinaryAccuracyConstructionStorage (inputSize controls cap profile)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def window (S A : ℕ) (words : BinaryAccuracyWords) : ℕ :=
  let ruler := BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator
  GeneralPaperBooleanRulerWorkStorage.window S words.denominator words.numerator +
    GeneralPaperMixedAccuracyCountStorage.window S A ruler.1 + fields S (controls A words) + 128 * S

theorem work_cap (S A : ℕ) (h : A ≤ S) (words : BinaryAccuracyWords) :
    (GeneralPaperBinaryAccuracy.prepare (fun w => w) A words).2 ≤
      GeneralPaperBinaryAccuracyConstructionStorage.price S (inputSize words) :=
  (GeneralPaperMeasuredInitializerMonotonicity.accuracy A S h words).trans
    (GeneralPaperBinaryAccuracyConstructionStorage.work S words)

theorem controls_cap (S A : ℕ) (h : A ≤ S) (words : BinaryAccuracyWords) :
    ∀ z ∈ controls A words, z ≤ cap S (inputSize words) := by
  let r := BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator
  let c := GeneralPaperBinaryAccuracy.count (fun w => w) A r.1
  have hL : r.1.length ≤ inputSize words := by
    have hl := GeneralPaperBinaryAccuracyConstructionStorage.ruler_length words
    dsimp only [r, inputSize] at *
    omega
  have hCount : c.1 ≤ inputSize words := by rw [GeneralPaperBinaryAccuracy.count_data]; exact hL
  have hc := GeneralPaperMixedAccuracyCountStorage.work_cap S A (inputSize words) h r.1 hL
  have hr := BinaryRulerPrecisionWork.prepare_work words.denominator words.numerator
  have hw := work_cap S A h words
  have hShape : (GeneralPaperBinaryAccuracy.prepare (fun w => w) A words).2 = r.2 * A + c.2 + 64 * A := rfl
  intro z hz
  simp only [controls, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold cap
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [r, c, inputSize] at *
  all_goals omega

theorem bounded (S A : ℕ) (h : A ≤ S) (words : BinaryAccuracyWords) :
    window S A words ≤ profile S (inputSize words) := by
  let r := BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator
  have hL : r.1.length ≤ inputSize words := by
    have hl := GeneralPaperBinaryAccuracyConstructionStorage.ruler_length words
    dsimp only [r, inputSize] at *
    omega
  have hR := GeneralPaperBooleanRulerWorkStorage.bounded S words.denominator words.numerator
  have hC := GeneralPaperMixedAccuracyCountStorage.bounded S A (inputSize words) h r.1 hL
  have hf := GeneralPaperExpressionArrayReturns.fields_mono_cap S (cap S (inputSize words))
    (controls A words) (controls_cap S A h words)
  change fields S _ ≤ 8 * (natBits (cap S (inputSize words)) + S) + 32 * S at hf
  unfold window profile
  dsimp only [r, inputSize] at *
  omega

theorem window_diagonal (S : ℕ) (words : BinaryAccuracyWords) :
    window S S words = GeneralPaperBinaryAccuracyConstructionStorage.window S words := by
  dsimp only [window, GeneralPaperBinaryAccuracyConstructionStorage.window]
  rw [GeneralPaperMixedAccuracyCountStorage.window_diagonal]

end Blotto.GeneralPaperMixedBinaryAccuracyStorage
