import Blotto.BinaryCarryCounterFinalization
import Blotto.BinaryPayloadMergeBitWork

/-! A register-word length uses the existing Boolean carry loop and decodes
only its final logarithmic counter. No natural position is incremented for each
input cell. Original numeric fields are retained. The separate allocation and
merge-size bounds are source certificates, not host allocator/GC calibration. -/
namespace Blotto.BinaryRegisterBooleanCount
open BinaryCarryCounter
set_option autoImplicit false
set_option maxHeartbeats 1500000

def bits (word : List Bool) : ℕ × ℕ :=
  let counter := count word [true]
  let nextLength := BinaryPayload.decode counter
  (nextLength-1,nextLength)

theorem bits_record (word : List Bool) : bits word = (word.length,word.length+1) := by
  have h := lengthFromOne_eq word
  change BinaryPayload.decode (count word [true]) = word.length+1 at h
  simp only [bits,h,Nat.add_sub_cancel]

theorem counter_value (word : List Bool) :
    value (count word [true]) = word.length+1 := by
  rw [count_value]
  change 1+word.length = word.length+1
  omega

theorem counter_width (word : List Bool) :
    (count word [true]).length ≤ binaryWordWidth (word.length+1) := countFromOne_length word

theorem counter_cells (word : List Bool) :
    1+countCarryCells word [true] ≤ 2*word.length+2 := by
  have h := lengthFromOne_carry_bound word
  omega

theorem counter_merges (word : List Bool) :
    BinaryPayload.mergeSize (count word [true]).length ≤ 8*(word.length+1) := counter_mergeSize_bound word

theorem count_append (first second counter : List Bool) :
    count (first++second) counter = count second (count first counter) := by
  induction first generalizing counter with
  | nil => rfl
  | cons bit rest ih => simpa only [List.cons_append,count] using ih (increment counter)

theorem reached_counter (word : List Bool) (used : ℕ) :
    count word [true] = count (word.drop used) (count (word.take used) [true]) := by
  have h := count_append (word.take used) (word.drop used) [true]
  rw [List.take_append_drop] at h
  exact h

theorem every_counter (word : List Bool) (used : ℕ) :
    value (count (word.take used) [true]) = (word.take used).length+1 ∧
      (count (word.take used) [true]).length ≤ binaryWordWidth (word.length+1) := by
  refine ⟨counter_value _,?_⟩
  exact (counter_width _).trans (binaryWordWidth_mono (by have h := List.length_take_le' used word; omega))

theorem retained_counter_cells (word : List Bool) (used : ℕ) :
    1+countCarryCells (word.take used) [true] ≤ 2*word.length+2 := by
  have h := counter_cells (word.take used)
  have hl := List.length_take_le' used word
  omega

-- Existing balanced-decoder bit-price interpretation at a fixed linear
-- primitive profile. This is not a certificate for host Nat primitives.
def decoderPrice (word : List Bool) : ℕ :=
  let counter := count word [true]
  BinaryPayload.balancedBitWork (fun w => 44*w) counter.toArray 0 counter.length

theorem counter_width_linear (word : List Bool) :
    (count word [true]).length ≤ 2*(word.length+1) := by
  have hw := counter_width word
  have hl := Nat.log2_le_self (word.length+1)
  unfold binaryWordWidth at hw
  omega

theorem decoder_price (word : List Bool) : decoderPrice word ≤ 744*(word.length+1) := by
  have hd := BinaryPayload.balancedBitWork_bound (fun w => 44*w) 44 (fun _ => Nat.le_refl _)
    (count word [true]).toArray 0 (count word [true]).length
  have hm := counter_merges word
  have hw := counter_width_linear word
  change decoderPrice word ≤ _ at hd
  nlinarith only [hd,hm,hw]

def sourcePrice (word : List Bool) : ℕ :=
  word.length+1+countCarryCells word [true]+decoderPrice word+2*(count word [true]).length

theorem source_price (word : List Bool) : sourcePrice word ≤ 752*(word.length+1) := by
  have hc := lengthFromOne_carry_bound word
  have hd := decoder_price word
  have hw := counter_width_linear word
  unfold sourcePrice
  nlinarith only [hc,hd,hw]

end Blotto.BinaryRegisterBooleanCount
