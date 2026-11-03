import Blotto.BinaryRatListFrame
import Blotto.RationalPRGRecognition
import Blotto.RationalPRGOriginalLattice
import Blotto.FixedArrayTable

/-! Portable game-input framing and native PRG recognition. The input format
stores field count, ordered budgets and exactly that many common values.
Frame parsing and promise checking remain distinct rejection stages. -/

namespace Blotto

structure BinaryGameWords where
  count : ℕ
  a : ℚ
  b : ℚ
  values : List ℚ

namespace BinaryGameWords

def valueTable (d : BinaryGameWords) (h : d.values.length = d.count) : FixedArrayTable d.count ℚ :=
  ⟨d.values.toArray, by simpa using h⟩

theorem valueTable_ofFn {n : ℕ} (a b : ℚ) (values : Fin n → ℚ) :
    (valueTable ⟨n, a, b, List.ofFn values⟩ (by simp)).read = values := by
  funext j
  simp [valueTable, FixedArrayTable.read]

end BinaryGameWords

namespace RationalPRGBinaryInput

def encode {n : ℕ} (i : RationalPRGOriginalInput n) : List Bool :=
  BinaryNatFrame.encode n ++ BinaryRatFrame.encode i.a ++ BinaryRatFrame.encode i.b ++
    BinaryRatListFrame.encode (List.ofFn i.values)

def read (bits : List Bool) : Option (BinaryGameWords × List Bool) :=
  (BinaryNatFrame.read bits).bind (fun dim => (BinaryRatFrame.read dim.2).bind (fun first =>
    (BinaryRatFrame.read first.2).bind (fun second =>
      (BinaryRatListFrame.read dim.1 second.2).map (fun row => (⟨dim.1, first.1, second.1, row.1⟩, row.2)))))

def readChecked (bits : List Bool) : Option ((Σ n, RationalPRGOriginalInput n) × List Bool) :=
  (read bits).bind (fun parsed =>
    if h : parsed.1.values.length = parsed.1.count then
      (checkRationalPRG (parsed.1.valueTable h).read parsed.1.a parsed.1.b).map
        (fun i => (⟨parsed.1.count, i⟩, parsed.2))
    else none)

theorem read_encode_append {n : ℕ} (i : RationalPRGOriginalInput n) (suffix : List Bool) :
    read (encode i ++ suffix) = some (⟨n, i.a, i.b, List.ofFn i.values⟩, suffix) := by
  have hRow := BinaryRatListFrame.read_encode_append (List.ofFn i.values) suffix
  simp only [List.length_ofFn] at hRow
  simp only [read, encode, List.append_assoc, BinaryNatFrame.read_encode_append,
    BinaryRatFrame.read_encode_append, Option.bind_some, hRow, Option.map_some]

theorem readChecked_encode_append {n : ℕ} (i : RationalPRGOriginalInput n) (suffix : List Bool) :
    readChecked (encode i ++ suffix) = some ((⟨n, i⟩ : Σ n, RationalPRGOriginalInput n), suffix) := by
  unfold readChecked
  rw [read_encode_append]
  simp only [Option.bind_some]
  rw [dite_eq_left (show (List.ofFn i.values).length = n by simp)]
  rw [BinaryGameWords.valueTable_ofFn, checkRationalPRG_complete]
  rfl

theorem encode_length {n : ℕ} (i : RationalPRGOriginalInput n) :
    (encode i).length = 2 * binaryWordWidth n + 3 + 2 * i.originalInputWordWidth + n := by
  simp only [encode, List.length_append, BinaryNatFrame.encode_length, BinaryRatFrame.encode_length,
    BinaryRatListFrame.encode_length, List.map_ofFn, List.length_ofFn, Function.comp_def, List.sum_ofFn,
    RationalPRGOriginalInput.originalInputWordWidth]
  omega

end RationalPRGBinaryInput
end Blotto
