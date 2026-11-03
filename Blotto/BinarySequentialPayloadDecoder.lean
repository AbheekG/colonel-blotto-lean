import Blotto.BinaryWordHighBit
import Blotto.BinaryFrameLogDecodingCost

/-! A balanced decoder consumes a borrowed Boolean list sequentially.
The second child receives the first child's actual returned tail. No array,
length scan, take/drop copy or numerical position is evaluated by the producer.
Missing leaves mark truncation; padding affects only a rejected numeric result.
Arithmetic/body prices and storage are supplied in separate source models. -/
namespace Blotto.BinarySequentialPayloadDecoder
set_option autoImplicit false

def run (length : ℕ) (bits : List Bool) : (ℕ × List Bool) × Bool :=
  if length = 0 then ((0,bits),true) else if length = 1 then
    match bits with
    | [] => ((0,[]),false)
    | bit::rest => ((if bit then 1 else 0,rest),true)
  else
    let low := length/2
    let first := run low bits
    let second := run (length-low) first.1.2
    ((first.1.1+(second.1.1 <<< low),second.1.2),first.2 && second.2)
termination_by length
decreasing_by all_goals omega

theorem run_tail (length : ℕ) (bits : List Bool) : (run length bits).1.2 = bits.drop length := by
  unfold run
  split
  · rename_i hz; simp only [hz,List.drop_zero]
  · split
    · rename_i hOne
      subst length
      cases bits <;> rfl
    · dsimp only
      rw [run_tail,run_tail,List.drop_drop]
      congr 1
      omega
termination_by length
decreasing_by all_goals omega

theorem run_valid (length : ℕ) (bits : List Bool) : (run length bits).2 = true ↔ length ≤ bits.length := by
  unfold run
  split
  · rename_i hz; simp only [hz,Nat.zero_le,true_iff]
  · split
    · rename_i hOne
      subst length
      cases bits <;> simp
    · dsimp only
      rw [Bool.and_eq_true,run_valid,run_valid,run_tail,List.length_drop]
      omega
termination_by length
decreasing_by all_goals omega

theorem run_value (length : ℕ) (bits : List Bool) (hLength : length ≤ bits.length) :
    (run length bits).1.1 = BinaryBigEndian.littleValue (bits.take length) := by
  unfold run
  split
  · rename_i hz
    simp only [hz,List.take_zero,BinaryBigEndian.littleValue]
  · split
    · rename_i hOne
      subst length
      cases bits with
      | nil => simp only [List.length_nil] at hLength; omega
      | cons bit rest => cases bit <;> rfl
    · dsimp only
      have hLow : length/2 ≤ bits.length := by omega
      have hHigh : length-length/2 ≤ (run (length/2) bits).1.2.length := by
        rw [run_tail,List.length_drop]
        omega
      rw [run_value (length/2) bits hLow,run_value (length-length/2) _ hHigh,run_tail]
      have hSplit : bits.take length = bits.take (length/2)++(bits.drop (length/2)).take (length-length/2) := by
        rw [← List.take_add]
        congr 1
        omega
      rw [hSplit,BinaryWordHighBit.littleValue_append,List.length_take, min_eq_left hLow,Nat.shiftLeft_eq]
      ring
termination_by length
decreasing_by all_goals omega

theorem run_merge_value (length : ℕ) (bits : List Bool) (hLength : 1 < length) :
    (run length bits).1.1 = (run (length/2) bits).1.1+
      ((run (length-length/2) (run (length/2) bits).1.2).1.1 <<< (length/2)) := by
  conv_lhs => unfold run
  rw [ite_eq_right (by omega),ite_eq_right (by omega)]

theorem run_bound (length : ℕ) (bits : List Bool) : (run length bits).1.1 < 2^length := by
  unfold run
  split
  · rename_i hz; simp [hz]
  · split
    · rename_i hOne
      subst length
      cases bits with
      | nil => decide
      | cons bit rest => cases bit <;> simp
    · dsimp only
      have hl := run_bound (length/2) bits
      have hh := run_bound (length-length/2) (run (length/2) bits).1.2
      have hPower : 2^length = 2^(length/2)*2^(length-length/2) := by
        rw [← pow_add]
        congr 1
        omega
      have hm := Nat.mul_le_mul_left (2^(length/2))
        (show (run (length-length/2) (run (length/2) bits).1.2).1.1+1 ≤ 2^(length-length/2) by omega)
      rw [Nat.shiftLeft_eq,hPower]
      nlinarith only [hl,hm]
termination_by length
decreasing_by all_goals omega

theorem run_accepted (length : ℕ) (bits : List Bool) (hLength : length ≤ bits.length) :
    run length bits = ((BinaryPayload.decode (bits.take length),bits.drop length),true) := by
  apply Prod.ext
  · apply Prod.ext
    · rw [run_value length bits hLength,BinaryBigEndian.littleValue_decode]
    · exact run_tail length bits
  · exact (run_valid length bits).mpr hLength

theorem run_rejected (length : ℕ) (bits : List Bool) (hLength : bits.length < length) :
    (run length bits).2 = false := by
  cases hv : (run length bits).2 with
  | false => rfl
  | true =>
      have h := (run_valid length bits).mp hv
      omega

def read (frame : List Bool) : Option (ℕ × List Bool) :=
  match BinaryNatFrame.scanWidth 0 frame with
  | none => none
  | some parsed =>
      let decoded := run parsed.1 parsed.2
      if decoded.2 then some decoded.1 else none

theorem read_refines (frame : List Bool) : read frame = BinaryNatFrame.read frame := by
  unfold read BinaryNatFrame.read
  cases hScan : BinaryNatFrame.scanWidth 0 frame with
  | none => rfl
  | some parsed =>
      rcases parsed with ⟨length,bits⟩
      simp only [Option.bind_some]
      by_cases hLength : length ≤ bits.length
      · rw [run_accepted length bits hLength]
        simp only [ite_true,hLength]
      · rw [run_rejected length bits (by omega)]
        simp only [Bool.false_eq_true,ite_false,hLength]

theorem read_encode (n : ℕ) (suffix : List Bool) :
    read (BinaryNatFrame.encode n++suffix) = some (n,suffix) := by
  rw [read_refines,BinaryNatFrame.read_encode_append]

theorem consumed_width (frame : List Bool) (length : ℕ) (bits : List Bool)
    (h : BinaryNatFrame.scanWidth 0 frame = some (length,bits)) : length ≤ frame.length := by
  have hs := BinaryNatFrame.scanWidth_length 0 frame length bits h
  omega

end Blotto.BinarySequentialPayloadDecoder
