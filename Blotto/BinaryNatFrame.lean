import Blotto.BinaryPayloadCounts

/-! Self-delimiting natural frames: w zero bits, a one-bit delimiter, then
w least-significant-first payload bits. The reader preserves trailing input
and rejects missing delimiters or truncated payloads. Zero uses w=1. -/

namespace Blotto.BinaryNatFrame

def encode (n : ℕ) : List Bool :=
  List.replicate (binaryWordWidth n) false ++ true :: BinaryPayload.bits (binaryWordWidth n) n

def scanWidth : ℕ → List Bool → Option (ℕ × List Bool)
  | _, [] => none
  | count, true :: rest => some (count, rest)
  | count, false :: rest => scanWidth (count + 1) rest

def read (frame : List Bool) : Option (ℕ × List Bool) :=
  (scanWidth 0 frame).bind (fun pair =>
    if pair.1 ≤ pair.2.length then some (BinaryPayload.decode (pair.2.take pair.1), pair.2.drop pair.1) else none)

theorem scanWidth_prefix (count width : ℕ) (suffix : List Bool) :
    scanWidth count (List.replicate width false ++ true :: suffix) = some (count + width, suffix) := by
  induction width generalizing count with
  | zero => simp [scanWidth]
  | succ width ih => simp [List.replicate_succ, scanWidth, ih, Nat.add_comm, Nat.add_left_comm]

theorem encode_length (n : ℕ) : (encode n).length = 2 * binaryWordWidth n + 1 := by
  simp [encode, BinaryPayload.bits_length]
  omega

theorem read_encode_append (n : ℕ) (suffix : List Bool) : read (encode n ++ suffix) = some (n, suffix) := by
  have hTake : (BinaryPayload.bits (binaryWordWidth n) n ++ suffix).take (binaryWordWidth n) =
      BinaryPayload.bits (binaryWordWidth n) n := by
    simpa only [BinaryPayload.bits_length] using (List.take_left (l₁ := BinaryPayload.bits (binaryWordWidth n) n) (l₂ := suffix))
  have hDrop : (BinaryPayload.bits (binaryWordWidth n) n ++ suffix).drop (binaryWordWidth n) = suffix := by
    simpa only [BinaryPayload.bits_length] using (List.drop_left (l₁ := BinaryPayload.bits (binaryWordWidth n) n) (l₂ := suffix))
  have hLength : binaryWordWidth n ≤ (BinaryPayload.bits (binaryWordWidth n) n ++ suffix).length := by
    simp [BinaryPayload.bits_length]
  simp only [read, encode, List.append_assoc, List.cons_append, scanWidth_prefix, Nat.zero_add,
    Option.bind_some, ite_eq_left hLength, hTake, hDrop]
  rw [BinaryPayload.decode_bits _ _ (lt_pow_binaryWordWidth n)]

theorem read_encode (n : ℕ) : read (encode n) = some (n, []) := by
  simpa using read_encode_append n []

theorem read_missing_delimiter (width : ℕ) : read (List.replicate width false) = none := by
  have hScan : ∀ count, scanWidth count (List.replicate width false) = none := by
    induction width with
    | zero => intro count; rfl
    | succ width ih => intro count; simp [List.replicate_succ, scanWidth, ih]
  simp only [read, hScan, Option.bind_none]

theorem read_truncated (width : ℕ) (payload : List Bool) (h : payload.length < width) :
    read (List.replicate width false ++ true :: payload) = none := by
  simp only [read, scanWidth_prefix, Nat.zero_add, Option.bind_some, ite_eq_right (by omega : ¬width ≤ payload.length)]

end Blotto.BinaryNatFrame
