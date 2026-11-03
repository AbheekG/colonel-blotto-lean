import Blotto.BinaryBalancedWordEncodingCost

/-! Source numeric-word retention for the actual cropped encoder. A frame
keeps all merge words and control lengths while either child runs; this even
overcounts the low tail call's discarded frame. Boolean cells, address/header
records and primitive-internal workspace are separate representation layers. -/

namespace Blotto.BinaryBalancedWordEncodingSpace
open BinaryBalancedWordEncoder BinaryBalancedWordEncodingCost
set_option autoImplicit false

def frameBits (length value : ℕ) : ℕ :=
  mergePrice (fun _ => 0) length value+binaryWordWidth length+
    binaryWordWidth (length/2)+binaryWordWidth (length-length/2)+4

theorem frame_bits_bound (length value : ℕ) (hLength : 1 < length) (hValue : value < 2^length) :
    frameBits length value ≤ 12*(length+1) := by
  have hm := merge_price_bound (fun _ => 0) 0 (by intro w; simp) length value hLength hValue
  have hn := Nat.log2_le_self length
  have hl := Nat.log2_le_self (length/2)
  have hh := Nat.log2_le_self (length-length/2)
  unfold frameBits binaryWordWidth
  norm_num only [Nat.mul_zero, Nat.add_zero, Nat.reduceAdd] at hm
  omega

def peak (length value : ℕ) : ℕ :=
  if length ≤ 1 then binaryWordWidth value+binaryWordWidth length+4 else
    frameBits length value+
      max (peak (length-length/2) (value >>> (length/2)))
        (peak (length/2) (masked value (length/2)))
termination_by length
decreasing_by all_goals omega

theorem peak_bound (length value : ℕ) (hValue : value < 2^length) :
    peak length value ≤ 48*length+24 := by
  rw [peak]
  split
  · rename_i hSmall
    have hn := Nat.log2_le_self length
    have hv : binaryWordWidth value ≤ length+1 := by
      by_cases hz : length = 0
      · subst length
        have he : value = 0 := by simpa only [pow_zero, Nat.lt_one_iff] using hValue
        simp only [he, binaryWordWidth, Nat.log2_zero]
        omega
      · exact (binaryWordWidth_le_of_lt_pow (by omega) hValue).trans (Nat.le_succ _)
    have hLen : binaryWordWidth length ≤ length+1 := by unfold binaryWordWidth; omega
    omega
  · rename_i hLarge
    have hLength : 1 < length := by omega
    have hf := frame_bits_bound length value hLength hValue
    have hl := peak_bound (length/2) (masked value (length/2)) (masked_bound value (length/2))
    have hh := peak_bound (length-length/2) (value >>> (length/2))
      (shifted_bound length (length/2) value (by omega) hValue)
    have hm : max (peak (length-length/2) (value >>> (length/2)))
        (peak (length/2) (masked value (length/2))) ≤ 36*length+12 := by
      apply max_le <;> omega
    omega
termination_by length
decreasing_by all_goals omega

def bitsPeak (value : ℕ) : ℕ := peak (binaryWordWidth value) value

theorem bits_peak_bound (value : ℕ) : bitsPeak value ≤ 48*binaryWordWidth value+24 :=
  peak_bound _ _ (lt_pow_binaryWordWidth value)

inductive RetainedPath : ℕ → ℕ → ℕ → Prop
  | frame (length value : ℕ) : RetainedPath length value
      (if length ≤ 1 then binaryWordWidth value+binaryWordWidth length+4 else frameBits length value)
  | high (length value retained : ℕ) (hLength : 1 < length)
      (child : RetainedPath (length-length/2) (value >>> (length/2)) retained) :
      RetainedPath length value (frameBits length value+retained)
  | low (length value retained : ℕ) (hLength : 1 < length)
      (child : RetainedPath (length/2) (masked value (length/2)) retained) :
      RetainedPath length value (frameBits length value+retained)

theorem retained_path_le_peak {length value retained : ℕ} (path : RetainedPath length value retained) :
    retained ≤ peak length value := by
  induction path with
  | frame length value =>
    by_cases h : length ≤ 1
    · rw [peak]
      simp only [ite_eq_left h, le_refl]
    · rw [peak]
      simp only [ite_eq_right h]
      omega
  | high length value retained hLength child ih =>
    rw [peak, ite_eq_right (by omega : ¬length ≤ 1)]
    exact Nat.add_le_add_left (ih.trans (le_max_left _ _)) _
  | low length value retained hLength child ih =>
    rw [peak, ite_eq_right (by omega : ¬length ≤ 1)]
    exact Nat.add_le_add_left (ih.trans (le_max_right _ _)) _

theorem bits_every_retained_path (value retained : ℕ)
    (path : RetainedPath (binaryWordWidth value) value retained) :
    retained ≤ 48*binaryWordWidth value+24 :=
  (retained_path_le_peak path).trans (bits_peak_bound value)

theorem output_and_numeric_peak (value : ℕ) (suffix : List Bool) :
    into (binaryWordWidth value) value suffix = BinaryPayload.bits (binaryWordWidth value) value++suffix ∧
    (into (binaryWordWidth value) value suffix).length = binaryWordWidth value+suffix.length ∧
    bitsPeak value ≤ 48*binaryWordWidth value+24 :=
  ⟨into_data _ _ _, into_length _ _ _, bits_peak_bound value⟩

end Blotto.BinaryBalancedWordEncodingSpace
