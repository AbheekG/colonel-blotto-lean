import Blotto.RationalPRGRequestReadBounds
import Blotto.RationalPRGParsedCheckCost

/-! A checked incoming game/request bounds the certified original input's
total reduced rational words. No canonical/minimal-frame assumption is used. -/

namespace Blotto.RationalPRGBinaryInput
open scoped BigOperators

theorem readChecked_inputWordWidth (frame : List Bool) (input : Σ n, RationalPRGOriginalInput n)
    (suffix : List Bool) (h : readChecked frame = some (input, suffix)) :
    input.2.originalInputWordWidth ≤ (frame.length + 2) * (4 * frame.length + 13) := by
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
        have hWidthEq := congrArg (fun p => p.1.2.originalInputWordWidth) hPair
        change i.originalInputWordWidth = input.2.originalInputWordWidth at hWidthEq
        have hData := checkRationalPRG_data (data.valueTable hCount).read data.a data.b i hCheck
        have hSizes := read_wordWidths frame data tail hRaw
        have hValues : ∀ j, rationalWordWidth (i.values j) ≤ 4 * frame.length + 13 := by
          intro j
          rw [hData.1]
          exact data.valueTable_wordWidth hCount _ hSizes.2.2.2.2 j
        have hSum : (∑ j, rationalWordWidth (i.values j)) ≤ data.count * (4 * frame.length + 13) := by
          calc
            _ ≤ ∑ _j : Fin data.count, (4 * frame.length + 13) := Finset.sum_le_sum (fun j _ => hValues j)
            _ = _ := by simp
        have hA : rationalWordWidth i.a ≤ 4 * frame.length + 13 := hData.2.1 ▸ hSizes.2.2.1
        have hB : rationalWordWidth i.b ≤ 4 * frame.length + 13 := hData.2.2 ▸ hSizes.2.2.2.1
        have hCountPrice := Nat.mul_le_mul_right (4 * frame.length + 13) hSizes.1
        rw [← hWidthEq]
        unfold RationalPRGOriginalInput.originalInputWordWidth
        nlinarith
    · cases h

end Blotto.RationalPRGBinaryInput
namespace Blotto.RationalPRGBinaryRequest

theorem readWords_inputWordWidth (frame : List Bool) (input : Σ n, RationalPRGOriginalInput n)
    (words : BinaryAccuracyWords) (suffix : List Bool)
    (h : readWords frame = some (input, words, suffix)) :
    input.2.originalInputWordWidth ≤ (frame.length + 2) * (4 * frame.length + 13) := by
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
      exact RationalPRGBinaryInput.readChecked_inputWordWidth frame parsedInput tail hGame

end Blotto.RationalPRGBinaryRequest
