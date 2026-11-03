import Blotto.BinaryCanonicalMagnitude
import Blotto.BinaryStoredRowFrameWork

/-! A natural dimension header is produced directly from existing Boolean
payloads: trim high zeros, retain one false bit at zero, and map/append the
width delimiter. No represented natural is decoded by the producer. Exact
canonical header bytes and source-length-derived Boolean/cell visits hold;
reader/index/header-cache ownership and complete model costs are separate. -/

namespace Blotto.BinaryStoredNatHeader
open BinaryCanonicalMagnitude

theorem littleValue_injective_of_length (first second : List Bool) (hLength : first.length = second.length)
    (hValue : BinaryBigEndian.littleValue first = BinaryBigEndian.littleValue second) : first = second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons head tail => simp only [List.length_nil,List.length_cons] at hLength; omega
  | cons bit rest ih =>
      cases second with
      | nil => simp only [List.length_cons,List.length_nil] at hLength; omega
      | cons head tail =>
          have hl : rest.length = tail.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hLength
          cases bit <;> cases head <;> simp only [BinaryBigEndian.littleValue,Bool.false_eq_true,ite_false,ite_true] at hValue
          · exact congrArg (List.cons false) (ih tail hl (by omega))
          · omega
          · omega
          · exact congrArg (List.cons true) (ih tail hl (by omega))

def payload (bits : List Bool) : List Bool :=
  let reduced := trim bits
  if reduced = [] then [false] else reduced

theorem payload_value (bits : List Bool) : BinaryBigEndian.littleValue (payload bits) = BinaryBigEndian.littleValue bits := by
  unfold payload
  dsimp only
  split
  · rename_i hZero
    have he := trim_value bits
    rw [hZero] at he
    exact he
  · exact trim_value bits

theorem payload_length_le (bits : List Bool) : (payload bits).length ≤ bits.length + 1 := by
  unfold payload
  dsimp only
  split
  · simp only [List.length_singleton]; omega
  · exact (trim_length bits).trans (Nat.le_succ _)

theorem payload_length (bits : List Bool) : (payload bits).length = binaryWordWidth (BinaryBigEndian.littleValue bits) := by
  unfold payload
  dsimp only
  split
  · rename_i hZero
    have he := trim_value bits
    rw [hZero] at he
    simp only [BinaryBigEndian.littleValue] at he
    rw [← he]
    rfl
  · rename_i hNonzero
    have hValue := trim_value bits
    have hUpper := trim_wordWidth bits
    have hPositive : BinaryBigEndian.littleValue bits ≠ 0 := by
      intro hz
      exact hNonzero (trim_zero bits hz)
    have hBound := BinaryBigEndian.value_bounds (trim bits).reverse
    rw [BinaryBigEndian.value_reverse,List.length_reverse,hValue] at hBound
    have hLog := (Nat.log2_lt hPositive).mpr hBound
    unfold binaryWordWidth at hUpper ⊢
    omega

theorem payload_state (bits : List Bool) : payload bits = BinaryPayload.bits (binaryWordWidth (BinaryBigEndian.littleValue bits)) (BinaryBigEndian.littleValue bits) := by
  apply littleValue_injective_of_length
  · rw [payload_length,BinaryPayload.bits_length]
  · rw [payload_value]
    have he : BinaryBigEndian.littleValue (BinaryPayload.bits (binaryWordWidth (BinaryBigEndian.littleValue bits)) (BinaryBigEndian.littleValue bits)) =
        BinaryBigEndian.littleValue bits := by
      rw [BinaryBigEndian.littleValue_decode,BinaryPayload.decode_bits _ _ (lt_pow_binaryWordWidth _)]
    exact he.symm

def header (bits : List Bool) : List Bool :=
  let stored := payload bits
  stored.map (fun _ => false) ++ true :: stored

theorem falseMap_eq (bits : List Bool) : bits.map (fun _ => false) = List.replicate bits.length false := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [List.map_cons,List.length_cons,List.replicate_succ,ih]

theorem header_state (bits : List Bool) : header bits = BinaryNatFrame.encode (BinaryBigEndian.littleValue bits) := by
  unfold header BinaryNatFrame.encode
  dsimp only
  rw [falseMap_eq,payload_length,payload_state]

theorem header_length (bits : List Bool) : (header bits).length = 2 * (payload bits).length + 1 := by
  simp only [header,List.length_append,List.length_map,List.length_cons]
  omega

def visits (bits : List Bool) : ℕ := bitWork bits + 4 * (payload bits).length + 3

theorem visits_bound (bits : List Bool) : visits bits ≤ 11 * bits.length + 12 := by
  have ht := bitWork_bound bits
  have hp := payload_length_le bits
  unfold visits
  omega

def prepare (bits : List Bool) : List Bool × ℕ := (header bits,visits bits)

theorem prepare_state (bits : List Bool) : (prepare bits).1 = BinaryNatFrame.encode (BinaryBigEndian.littleValue bits) := header_state bits

theorem prepare_bound (bits : List Bool) : (prepare bits).2 ≤ 11 * bits.length + 12 := visits_bound bits

end Blotto.BinaryStoredNatHeader
