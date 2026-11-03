import Blotto.RationalPRGBinaryRequest
import Blotto.BinaryDecodedRationalSize

/-! Request sizes are controlled by incoming bits, including nonminimal
frames. Checked game counts, accuracy suffixes and selected precision have
bounds needed for request bookkeeping and bounded seed preparation. -/

namespace Blotto.RationalPRGBinaryInput

theorem read_suffix_length (frame : List Bool) (data : BinaryGameWords) (suffix : List Bool)
    (h : read frame = some (data, suffix)) : suffix.length ≤ frame.length := by
  unfold read at h
  cases hDim : BinaryNatFrame.read frame with
  | none => rw [hDim, Option.bind_none] at h; cases h
  | some dim =>
    rcases dim with ⟨count, tail⟩
    rw [hDim, Option.bind_some] at h
    cases hA : BinaryRatFrame.read tail with
    | none => rw [hA, Option.bind_none] at h; cases h
    | some first =>
      rcases first with ⟨a, rest⟩
      rw [hA, Option.bind_some] at h
      cases hB : BinaryRatFrame.read rest with
      | none => rw [hB, Option.bind_none] at h; cases h
      | some second =>
        rcases second with ⟨b, remaining⟩
        rw [hB, Option.bind_some] at h
        cases hRow : BinaryRatListFrame.read count remaining with
        | none => rw [hRow, Option.map_none] at h; cases h
        | some row =>
          rcases row with ⟨values, last⟩
          rw [hRow, Option.map_some] at h
          cases Option.some.inj h
          exact (BinaryRatListFrame.read_suffix_length count remaining values last hRow).trans
            ((BinaryRatFrame.read_suffix_length rest b remaining hB).trans
              ((BinaryRatFrame.read_suffix_length tail a rest hA).trans
                (BinaryNatFrame.read_suffix_length frame count tail hDim)))

theorem readChecked_bounds (frame : List Bool) (input : Σ n, RationalPRGOriginalInput n) (suffix : List Bool)
    (h : readChecked frame = some (input, suffix)) : input.1 ≤ frame.length ∧ suffix.length ≤ frame.length := by
  unfold readChecked at h
  cases hRaw : read frame with
  | none => rw [hRaw, Option.bind_none] at h; cases h
  | some parsed =>
    rcases parsed with ⟨data, tail⟩
    rw [hRaw, Option.bind_some] at h
    split at h
    · rename_i hCount
      cases hCheck : checkRationalPRG (data.valueTable hCount).read data.a data.b with
      | none => rw [hCheck, Option.map_none] at h; cases h
      | some i =>
        rw [hCheck, Option.map_some] at h
        have hPair := Option.some.inj h
        have hn := congrArg (fun p => p.1.1) hPair
        have ht := congrArg Prod.snd hPair
        have hCountBound := (read_wordWidths frame data tail hRaw).1
        have hTail := read_suffix_length frame data tail hRaw
        change data.count = input.1 at hn
        change tail = suffix at ht
        exact ⟨hn ▸ hCountBound, ht ▸ hTail⟩
    · cases h

end Blotto.RationalPRGBinaryInput
namespace Blotto.BinaryAccuracyWords

theorem precision_width_bound (a : BinaryAccuracyWords) : a.precision ≤ a.denominator.width + 6 := by
  unfold precision
  rw [PositiveBinaryWord.ratioPrecision_refines]
  unfold PositiveBinaryWord.ratioPrecisionNumeric
  rw [PositiveBinaryWord.width_shifted]
  dsimp only
  split <;> omega

end Blotto.BinaryAccuracyWords
namespace Blotto.RationalPRGBinaryRequest

theorem readWords_bounds (frame : List Bool) (input : Σ n, RationalPRGOriginalInput n)
    (words : BinaryAccuracyWords) (suffix : List Bool)
    (h : readWords frame = some (input, words, suffix)) :
    input.1 ≤ frame.length ∧ suffix.length ≤ frame.length ∧ words.precision ≤ frame.length + 6 := by
  unfold readWords at h
  cases hGame : RationalPRGBinaryInput.readChecked frame with
  | none => rw [hGame, Option.bind_none] at h; cases h
  | some game =>
    rcases game with ⟨parsedInput, tail⟩
    rw [hGame, Option.bind_some] at h
    cases hAccuracy : BinaryAccuracyWords.read tail with
    | none => rw [hAccuracy, Option.map_none] at h; cases h
    | some accuracy =>
      rcases accuracy with ⟨parsedWords, rest⟩
      rw [hAccuracy, Option.map_some] at h
      cases Option.some.inj h
      have hGameBounds := RationalPRGBinaryInput.readChecked_bounds frame parsedInput tail hGame
      have hAccuracyBounds := BinaryAccuracyWords.read_width_bound tail rest parsedWords hAccuracy
      have hPrecision := parsedWords.precision_width_bound
      dsimp only
      exact ⟨hGameBounds.1, by omega, by omega⟩

theorem accepted_seed_budget_bound (frame : List Bool) (input : Σ n, RationalPRGOriginalInput n)
    (words : BinaryAccuracyWords) (suffix : List Bool)
    (h : readWords frame = some (input, words, suffix)) :
    RationalLottoResourceSystem.sampleBitBudget input.1 words.precision ≤ 8 * frame.length + 3030 := by
  have hBounds := readWords_bounds frame input words suffix h
  rw [RationalLottoResourceSystem.sampleBitBudget_eq]
  omega

end Blotto.RationalPRGBinaryRequest
