import Blotto.BinaryRatListFrame
import Blotto.ProductRawSecurityState

/-! A retained whole-row observation has a finite self-delimiting bit frame.
Both complete rational rows and the selected field survive suffix-preserving
readback. No guide, tape or row closure is required in the serialized data.
These are representation/readback statements, not encoder/reader work prices. -/

namespace Blotto.BinaryWholeObservationFrame
open ProductSecurityTrainer

def restoreRow (m : ℕ) (row : List ℚ) : Option (Fin m → ℚ) :=
  if hLength : row.length = m then
    some (fun field => row[field.val]'(by rw [hLength]; exact field.isLt))
  else none

theorem restoreRow_ofFn {m : ℕ} (row : Fin m → ℚ) :
    restoreRow m (List.ofFn row) = some row := by
  unfold restoreRow
  simp only [List.length_ofFn, dite_true]
  congr 1
  funext field
  simp only [List.getElem_ofFn]

def encode {m : ℕ} (observed : RawObservation m) : List Bool :=
  BinaryRatListFrame.encodeRow observed.1 ++
    BinaryRatListFrame.encodeRow observed.2.1 ++ BinaryNatFrame.encode observed.2.2.val

def read (m : ℕ) (bits : List Bool) : Option (RawObservation m × List Bool) :=
  (BinaryRatListFrame.readRow bits).bind (fun first =>
    (BinaryRatListFrame.readRow first.2.2).bind (fun second =>
      (BinaryNatFrame.read second.2.2).bind (fun field =>
        if first.1 = m ∧ second.1 = m then
          (restoreRow m first.2.1).bind (fun firstRow =>
            (restoreRow m second.2.1).bind (fun secondRow =>
              if hField : field.1 < m then some ((firstRow, secondRow, ⟨field.1, hField⟩), field.2)
              else none))
        else none)))

theorem read_encode_append {m : ℕ} (observed : RawObservation m) (suffix : List Bool) :
    read m (encode observed ++ suffix) = some (observed, suffix) := by
  simp only [read, encode, List.append_assoc, BinaryRatListFrame.readRow_encode_append,
    Option.bind_some, BinaryNatFrame.read_encode_append, restoreRow_ofFn,
    and_self, ite_true, observed.2.2.isLt, dite_true]

def encodeHistory {m : ℕ} (past : List (RawObservation m)) : List Bool :=
  BinaryNatFrame.encode past.length ++ past.flatMap encode

def readHistoryOf (m : ℕ) : ℕ → List Bool → Option (List (RawObservation m) × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits =>
      (read m bits).bind (fun first =>
        (readHistoryOf m count first.2).map (fun rest => (first.1 :: rest.1, rest.2)))

def readHistory (m : ℕ) (bits : List Bool) : Option (List (RawObservation m) × List Bool) :=
  (BinaryNatFrame.read bits).bind (fun first => readHistoryOf m first.1 first.2)

theorem readHistoryOf_encode_append {m : ℕ} (past : List (RawObservation m)) (suffix : List Bool) :
    readHistoryOf m past.length (past.flatMap encode ++ suffix) = some (past, suffix) := by
  induction past with
  | nil => rfl
  | cons first past ih =>
    simp only [List.flatMap_cons, List.length_cons, List.append_assoc, readHistoryOf,
      read_encode_append, Option.bind_some, ih, Option.map_some]

theorem readHistory_encode_append {m : ℕ} (past : List (RawObservation m)) (suffix : List Bool) :
    readHistory m (encodeHistory past ++ suffix) = some (past, suffix) := by
  simp only [readHistory, encodeHistory, List.append_assoc, BinaryNatFrame.read_encode_append,
    Option.bind_some, readHistoryOf_encode_append]

theorem encode_length {m : ℕ} (observed : RawObservation m) :
    (encode observed).length =
      (2 * binaryWordWidth m + 1 + 2 * (List.ofFn (fun field => rationalWordWidth (observed.1 field))).sum + m) +
      (2 * binaryWordWidth m + 1 + 2 * (List.ofFn (fun field => rationalWordWidth (observed.2.1 field))).sum + m) +
      (2 * binaryWordWidth observed.2.2.val + 1) := by
  simp only [encode, List.length_append, BinaryRatListFrame.encodeRow_length, BinaryNatFrame.encode_length]

theorem encodeHistory_length {m : ℕ} (past : List (RawObservation m)) :
    (encodeHistory past).length = 2 * binaryWordWidth past.length + 1 +
      (past.map (fun observed => (encode observed).length)).sum := by
  simp only [encodeHistory, List.length_append, BinaryNatFrame.encode_length,
    List.length_flatMap]

end Blotto.BinaryWholeObservationFrame
