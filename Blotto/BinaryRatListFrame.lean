import Blotto.BinaryRatFrame

/-! Rational sequences and dimensioned rows have suffix-preserving readers.
This is a complete bit format, using actual minimal coordinate word widths. -/

namespace Blotto.BinaryRatListFrame

def encode (values : List ℚ) : List Bool := values.flatMap BinaryRatFrame.encode

def read : ℕ → List Bool → Option (List ℚ × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits =>
    (BinaryRatFrame.read bits).bind (fun first =>
      (read count first.2).map (fun rest => (first.1 :: rest.1, rest.2)))

theorem read_encode_append (values : List ℚ) (suffix : List Bool) :
    read values.length (encode values ++ suffix) = some (values, suffix) := by
  induction values with
  | nil => rfl
  | cons q values ih =>
    simp only [encode] at ih
    simp only [encode, List.flatMap_cons, List.length_cons, List.append_assoc, read,
      BinaryRatFrame.read_encode_append, Option.bind_some, ih, Option.map_some]

theorem encode_length (values : List ℚ) :
    (encode values).length = 2 * (values.map rationalWordWidth).sum + values.length := by
  induction values with
  | nil => simp [encode]
  | cons q values ih =>
    simp only [encode, List.flatMap_cons, List.length_append, BinaryRatFrame.encode_length,
      List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

def encodeRow {n : ℕ} (row : Fin n → ℚ) : List Bool := BinaryNatFrame.encode n ++ encode (List.ofFn row)

def readRow (bits : List Bool) : Option (ℕ × List ℚ × List Bool) :=
  (BinaryNatFrame.read bits).bind (fun first =>
    (read first.1 first.2).map (fun rest => (first.1, rest.1, rest.2)))

theorem readRow_encode_append {n : ℕ} (row : Fin n → ℚ) (suffix : List Bool) :
    readRow (encodeRow row ++ suffix) = some (n, List.ofFn row, suffix) := by
  have hRead := read_encode_append (List.ofFn row) suffix
  simp only [List.length_ofFn] at hRead
  simp only [readRow, encodeRow, List.append_assoc, BinaryNatFrame.read_encode_append,
    Option.bind_some, hRead, Option.map_some]

theorem encodeRow_length {n : ℕ} (row : Fin n → ℚ) :
    (encodeRow row).length = 2 * binaryWordWidth n + 1 + 2 * (List.ofFn (fun j => rationalWordWidth (row j))).sum + n := by
  simp only [encodeRow, List.length_append, BinaryNatFrame.encode_length, encode_length,
    List.map_ofFn, List.length_ofFn, Function.comp_def]
  omega

end Blotto.BinaryRatListFrame
