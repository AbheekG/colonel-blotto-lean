import Blotto.RationalPRGParsedCheckCost
import Blotto.RationalPRGRequestReadBounds
import Blotto.AccuracyCounterBitCost
import Blotto.RationalPRGSeedPreparationWork

/-! Combines selected game parsing/promise checks, word accuracy/precision,
and exact seed preparation on the primary request's actual branches. Accuracy
precision is conservatively charged before the final empty-suffix gate. Sampler
processing/output, remaining metadata, backend and physical ownership/space
are separate. Bounds include malformed requests and wrong-length seeds. -/

namespace Blotto.RationalPRGBinaryRequest

def readPrecisionBitWork (model : RationalCostModel) (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  RationalPRGBinaryInput.checkedDecodingBitWork model primitive frame +
    match RationalPRGBinaryInput.readChecked frame with
    | none => 0
    | some game => BinaryAccuracyWords.readPrecisionBitWork primitive game.2

def readPrecisionBound (model : RationalCostModel) (c length : ℕ) : ℕ :=
  RationalPRGBinaryInput.decodingBound model c length +
    RationalPRGBinaryInput.parsedRecognitionBound model length + (127 + 48 * c) * length + 634 + 240 * c

theorem readPrecisionBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    readPrecisionBitWork model primitive frame ≤ readPrecisionBound model c frame.length := by
  have hGame := RationalPRGBinaryInput.checkedDecodingBitWork_bound model primitive c hPrimitive frame
  unfold readPrecisionBitWork
  cases hRead : RationalPRGBinaryInput.readChecked frame with
  | none => simp only; unfold readPrecisionBound; omega
  | some game =>
    rcases game with ⟨input, suffix⟩
    have hSuffix := (RationalPRGBinaryInput.readChecked_bounds frame input suffix hRead).2
    have hAccuracy := BinaryAccuracyWords.readPrecisionBitWork_bound primitive c hPrimitive suffix
    have hPrice := Nat.mul_le_mul_left (127 + 48 * c) hSuffix
    simp only
    unfold readPrecisionBound
    omega

def preparationBitWork (model : RationalCostModel) (primitive : ℕ → ℕ) (frame seed : List Bool) : ℕ :=
  readPrecisionBitWork model primitive frame +
    match readWords frame with
    | none => 0
    | some parsed =>
      if parsed.2.2 = [] then
        seedPreparationBitWork primitive (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 parsed.2.1.precision) seed
      else 0

def seedPreparationBound (c requestLength seedLength : ℕ) : ℕ :=
  (seedLength + 1) * ((c + 2) * binaryWordWidth (seedLength + 1) + 1) +
    c * max (binaryWordWidth seedLength) (binaryWordWidth (8 * requestLength + 3030)) + 2 * seedLength

theorem preparationBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame seed : List Bool) :
    preparationBitWork model primitive frame seed ≤ readPrecisionBound model c frame.length +
      seedPreparationBound c frame.length seed.length := by
  have hRead := readPrecisionBitWork_bound model primitive c hPrimitive frame
  unfold preparationBitWork
  cases hParsed : readWords frame with
  | none => simp only; omega
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    have hSeedCount := accepted_seed_budget_bound frame input words suffix hParsed
    have hSeed := seedPreparationBitWork_bound primitive c hPrimitive
      (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed
    have hWidth := binaryWordWidth_mono hSeedCount
    have hPrice := Nat.mul_le_mul_left c
      (show max (binaryWordWidth seed.length) (binaryWordWidth (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision)) ≤
        max (binaryWordWidth seed.length) (binaryWordWidth (8 * frame.length + 3030)) by omega)
    simp only
    split
    · unfold seedPreparationBound
      omega
    · omega

theorem preparationBitWork_read_failure (model : RationalCostModel) (primitive : ℕ → ℕ) (frame seed : List Bool)
    (h : readWords frame = none) : preparationBitWork model primitive frame seed = readPrecisionBitWork model primitive frame := by
  simp only [preparationBitWork, h, Nat.add_zero]

end Blotto.RationalPRGBinaryRequest
