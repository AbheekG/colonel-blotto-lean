import Blotto.PositiveBinaryWord
import Blotto.BinaryNatFrame
import Blotto.UnaryPayloadReversed

/-! Positive words are extracted directly from framed Boolean payloads.
Leading zeros are accepted and removed; no payload integer is assembled. -/

namespace Blotto

namespace BinaryBigEndian

theorem trim_head_true (bits rest : List Bool) (head : Bool) (h : trim bits = head :: rest) : head = true := by
  induction bits with
  | nil => simp [trim] at h
  | cons b bits ih =>
    cases b
    · simp only [trim, List.dropWhile_cons, Bool.not_false, ite_true] at h
      exact ih h
    · simp only [trim, List.dropWhile_cons, Bool.not_true] at h
      exact (List.cons.inj h).1.symm

end BinaryBigEndian

namespace PositiveBinaryWord

def parse (bits : List Bool) : Option PositiveBinaryWord :=
  match BinaryBigEndian.trim bits with
  | true :: tail => some ⟨tail⟩
  | _ => none

theorem parse_of_pos (bits : List Bool) (hPos : 0 < BinaryBigEndian.value bits) :
    ∃ w, parse bits = some w ∧ w.value = BinaryBigEndian.value bits ∧ w.width ≤ bits.length := by
  have hValue := BinaryBigEndian.value_trim bits
  have hLength := BinaryBigEndian.trim_length bits
  cases hTrim : BinaryBigEndian.trim bits with
  | nil => rw [hTrim] at hValue; simp only [BinaryBigEndian.value] at hValue; omega
  | cons head tail =>
    have hh := BinaryBigEndian.trim_head_true bits tail head hTrim
    subst head
    refine ⟨⟨tail⟩, ?_, ?_, ?_⟩
    · rw [parse, hTrim]
    · rw [hTrim] at hValue
      exact hValue
    · rw [hTrim] at hLength
      exact hLength

def readPayloadNumeric (frame : List Bool) : Option (List Bool × List Bool) :=
  (BinaryNatFrame.scanWidth 0 frame).bind (fun pair =>
    if pair.1 ≤ pair.2.length then some (pair.2.take pair.1, pair.2.drop pair.1) else none)

def readPayload (frame : List Bool) : Option (List Bool × List Bool) := UnaryPayload.read frame

theorem readPayload_refines (frame : List Bool) : readPayload frame = readPayloadNumeric frame :=
  UnaryPayload.read_refines frame

def readReference (frame : List Bool) : Option (PositiveBinaryWord × List Bool) :=
  (readPayloadNumeric frame).bind (fun pair => (parse pair.1.reverse).map (fun w => (w, pair.2)))

def read (frame : List Bool) : Option (PositiveBinaryWord × List Bool) :=
  (UnaryPayload.readReversed frame).bind (fun pair => (parse pair.1).map (fun w => (w, pair.2)))

theorem read_eq_payload (frame : List Bool) : read frame =
    (readPayload frame).bind (fun pair => (parse pair.1.reverse).map (fun w => (w, pair.2))) := by
  rw [read, UnaryPayload.readReversed_refines]
  change ((readPayload frame).map (fun pair => (pair.1.reverse, pair.2))).bind _ = _
  cases h : readPayload frame <;> rfl

theorem read_refines_reference (frame : List Bool) : read frame = readReference frame := by
  rw [read_eq_payload, readPayload_refines]
  rfl

theorem readPayload_encode_append (n : ℕ) (suffix : List Bool) :
    readPayload (BinaryNatFrame.encode n ++ suffix) = some (BinaryPayload.bits (binaryWordWidth n) n, suffix) := by
  have hTake : (BinaryPayload.bits (binaryWordWidth n) n ++ suffix).take (binaryWordWidth n) =
      BinaryPayload.bits (binaryWordWidth n) n := by
    simpa only [BinaryPayload.bits_length] using (List.take_left (l₁ := BinaryPayload.bits (binaryWordWidth n) n) (l₂ := suffix))
  have hDrop : (BinaryPayload.bits (binaryWordWidth n) n ++ suffix).drop (binaryWordWidth n) = suffix := by
    simpa only [BinaryPayload.bits_length] using (List.drop_left (l₁ := BinaryPayload.bits (binaryWordWidth n) n) (l₂ := suffix))
  have hLength : binaryWordWidth n ≤ (BinaryPayload.bits (binaryWordWidth n) n ++ suffix).length := by
    simp [BinaryPayload.bits_length]
  rw [readPayload_refines]
  simp only [readPayloadNumeric, BinaryNatFrame.encode, List.append_assoc, List.cons_append,
    BinaryNatFrame.scanWidth_prefix, Nat.zero_add, Option.bind_some, ite_eq_left hLength, hTake, hDrop]

theorem read_encode_append (n : ℕ) (hN : 0 < n) (suffix : List Bool) :
    ∃ w, read (BinaryNatFrame.encode n ++ suffix) = some (w, suffix) ∧ w.value = n := by
  have hValue : BinaryBigEndian.value (BinaryPayload.bits (binaryWordWidth n) n).reverse = n := by
    rw [BinaryBigEndian.value_reverse_decode, BinaryPayload.decode_bits _ _ (lt_pow_binaryWordWidth n)]
  rcases parse_of_pos _ (by rw [hValue]; exact hN) with ⟨w, hParse, hw, _⟩
  refine ⟨w, ?_, hw.trans hValue⟩
  rw [read_eq_payload]
  simp only [readPayload_encode_append, Option.bind_some, hParse, Option.map_some]

theorem parse_sound (bits : List Bool) (w : PositiveBinaryWord) (h : parse bits = some w) :
    w.value = BinaryBigEndian.value bits := by
  have hValue := BinaryBigEndian.value_trim bits
  unfold parse at h
  cases ht : BinaryBigEndian.trim bits with
  | nil => rw [ht] at h; cases h
  | cons head tail =>
    rw [ht] at h hValue
    cases head
    · cases h
    · cases Option.some.inj h
      exact hValue

theorem readPayload_decode (frame : List Bool) :
    (readPayload frame).map (fun pair => (BinaryPayload.decode pair.1, pair.2)) = BinaryNatFrame.read frame := by
  rw [readPayload_refines]
  unfold readPayloadNumeric BinaryNatFrame.read
  cases h : BinaryNatFrame.scanWidth 0 frame with
  | none => rfl
  | some pair =>
    rcases pair with ⟨width, rest⟩
    dsimp only [Option.bind_some]
    split <;> rfl

theorem read_sound (frame suffix : List Bool) (w : PositiveBinaryWord) (h : read frame = some (w, suffix)) :
    BinaryNatFrame.read frame = some (w.value, suffix) := by
  have hDecode := readPayload_decode frame
  rw [read_eq_payload] at h
  cases hp : readPayload frame with
  | none => rw [hp] at h; cases h
  | some pair =>
    rcases pair with ⟨payload, tail⟩
    rw [hp, Option.bind_some] at h
    cases hs : parse payload.reverse with
    | none => rw [hs] at h; cases h
    | some parsed =>
      rw [hs] at h
      cases Option.some.inj h
      have hValue := parse_sound payload.reverse w hs
      rw [BinaryBigEndian.value_reverse_decode] at hValue
      rw [hp, Option.map_some] at hDecode
      simpa only [hValue] using hDecode.symm

theorem read_complete (frame suffix : List Bool) (n : ℕ) (hN : 0 < n)
    (h : BinaryNatFrame.read frame = some (n, suffix)) :
    ∃ w, read frame = some (w, suffix) ∧ w.value = n := by
  have hDecode := readPayload_decode frame
  rw [h] at hDecode
  cases hp : readPayload frame with
  | none => rw [hp] at hDecode; cases hDecode
  | some pair =>
    rcases pair with ⟨payload, tail⟩
    rw [hp, Option.map_some] at hDecode
    have hPair := Option.some.inj hDecode
    have hValue : BinaryBigEndian.value payload.reverse = n := by
      rw [BinaryBigEndian.value_reverse_decode]
      exact (Prod.mk.inj hPair).1
    have hTail : tail = suffix := (Prod.mk.inj hPair).2
    rcases parse_of_pos payload.reverse (by rw [hValue]; exact hN) with ⟨w, hw, hv, _⟩
    refine ⟨w, ?_, hv.trans hValue⟩
    rw [read_eq_payload]
    simp only [hp, Option.bind_some, hw, Option.map_some, hTail]

end PositiveBinaryWord
end Blotto
