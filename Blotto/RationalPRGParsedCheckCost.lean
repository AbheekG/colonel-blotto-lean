import Blotto.BinaryDecodedRationalSize
import Blotto.RationalPRGCheckSelectedWork
import Blotto.RationalPRGInputDecodingCost

/-! Successful raw game parsing bounds every promise-check operand and the
field count by incoming bits. The checked-reader observer charges actual
selected stages after its length gate. Table construction, numeric counters,
addressing, backend and ownership remain separate. -/

namespace Blotto.RationalPRGCheckCode

theorem recognitionWidth_mono {n N s S : ℕ} (hn : n ≤ N) (hs : s ≤ S) :
    recognitionWidth n s ≤ recognitionWidth N S := by
  have hDepth := Nat.mul_le_mul_right (2 ^ 2) (Nat.add_le_add_right hs 1)
  have hSum := Nat.mul_le_mul (Nat.add_le_add_right hs 1) hn
  unfold recognitionWidth expressionHeightBudget
  omega

end Blotto.RationalPRGCheckCode
namespace Blotto.BinaryGameWords
open scoped BigOperators

theorem valueTable_wordWidth (data : BinaryGameWords) (h : data.values.length = data.count) (W : ℕ)
    (hValues : ∀ q ∈ data.values, rationalWordWidth q ≤ W) (j : Fin data.count) :
    rationalWordWidth ((data.valueTable h).read j) ≤ W := by
  have hj : j.val < data.values.length := by omega
  have hRead : (data.valueTable h).read j = data.values[j.val]'hj := by
    simp [valueTable, FixedArrayTable.read]
  rw [hRead]
  exact hValues _ (List.getElem_mem hj)

end Blotto.BinaryGameWords
namespace Blotto.RationalPRGBinaryInput
open scoped BigOperators

def parsedRecognitionBound (model : RationalCostModel) (length : ℕ) : ℕ :=
  (19 * length + 23) * model.rat
    (RationalPRGCheckCode.recognitionWidth length (3 + (length + 2) * (4 * length + 13)))

theorem parsedSelectedCheckWork_bound (model : RationalCostModel) (frame : List Bool)
    (data : BinaryGameWords) (suffix : List Bool) (h : read frame = some (data, suffix))
    (hCount : data.values.length = data.count) :
    RationalPRGCheckCode.selectedBitWork model (data.valueTable hCount).read data.a data.b ≤
      parsedRecognitionBound model frame.length := by
  have hSizes := read_wordWidths frame data suffix h
  have hValues := fun j => data.valueTable_wordWidth hCount _ hSizes.2.2.2.2 j
  have hSum : (∑ j, rationalWordWidth ((data.valueTable hCount).read j)) ≤ data.count * (4 * frame.length + 13) := by
    calc
      _ ≤ ∑ _j : Fin data.count, (4 * frame.length + 13) := Finset.sum_le_sum (fun j _ => hValues j)
      _ = _ := by simp
  have hInput : RationalPRGCheckCode.inputWordWidth (data.valueTable hCount).read data.a data.b ≤
      (frame.length + 2) * (4 * frame.length + 13) := by
    have hCountPrice := Nat.mul_le_mul_right (4 * frame.length + 13) hSizes.1
    unfold RationalPRGCheckCode.inputWordWidth
    nlinarith [hSizes.2.2.1, hSizes.2.2.2.1]
  have hW := RationalPRGCheckCode.recognitionWidth_mono hSizes.1 (Nat.add_le_add_left hInput 3)
  exact (RationalPRGCheckCode.selectedBitWork_original_bound model (data.valueTable hCount).read data.a data.b).trans
    (Nat.mul_le_mul (by omega) (model.monotone hW))

def checkedDecodingBitWork (model : RationalCostModel) (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  decodingBitWork model primitive frame +
    match read frame with
    | none => 0
    | some parsed =>
      if h : parsed.1.values.length = parsed.1.count then
        RationalPRGCheckCode.selectedBitWork model (parsed.1.valueTable h).read parsed.1.a parsed.1.b
      else 0

theorem checkedDecodingBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    checkedDecodingBitWork model primitive frame ≤
      decodingBound model c frame.length + parsedRecognitionBound model frame.length := by
  have hDecode := decodingBitWork_bound model primitive c hPrimitive frame
  unfold checkedDecodingBitWork
  cases hParsed : read frame with
  | none => simp only; omega
  | some parsed =>
    rcases parsed with ⟨data, suffix⟩
    simp only
    split
    · rename_i hCount
      exact Nat.add_le_add hDecode (parsedSelectedCheckWork_bound model frame data suffix hParsed hCount)
    · omega

end Blotto.RationalPRGBinaryInput
