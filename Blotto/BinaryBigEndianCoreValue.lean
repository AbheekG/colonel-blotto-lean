import Blotto.BinaryPayloadCore

/-! Numerical specifications for direct most-significant-first word scans.
These specifications are not invoked by the accuracy selector's runtime. -/

namespace Blotto.BinaryBigEndian

def value : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 2 ^ rest.length else 0) + value rest

def littleValue : List Bool → ℕ
  | [] => 0
  | b :: rest => 2 * littleValue rest + if b then 1 else 0

theorem value_bounds (bits : List Bool) : value bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [value]
  | cons b rest ih =>
    simp only [value, List.length_cons, pow_succ]
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, zero_add] <;> omega

theorem value_append (a b : List Bool) : value (a ++ b) = value a * 2 ^ b.length + value b := by
  induction a with
  | nil => simp [value]
  | cons bit rest ih =>
    simp only [List.cons_append, value, List.length_append, ih, pow_add]
    cases bit <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring

theorem value_false_prefix (bits : List Bool) : value (false :: bits) = value bits := by simp [value]

theorem value_reverse (bits : List Bool) : value bits.reverse = littleValue bits := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
    rw [List.reverse_cons, value_append, ih]
    simp only [List.length_singleton, pow_one, value, List.length_nil, pow_zero, littleValue]
    ring

theorem littleValue_payload (bits : List Bool) :
    BinaryPayload.value (fun j => bits.getD j false) 0 bits.length = littleValue bits := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
    have hTail : BinaryPayload.value (fun j => (b :: rest).getD j false) 1 rest.length =
        BinaryPayload.value (fun j => rest.getD j false) 0 rest.length := by
      apply BinaryPayload.value_congr
      intro j
      simp [List.getD, Nat.add_comm]
    simp only [List.length_cons, BinaryPayload.value, Nat.zero_add, List.getD_cons_zero, hTail, ih, littleValue]

theorem littleValue_decode (bits : List Bool) : littleValue bits = BinaryPayload.decode bits := by
  rw [BinaryPayload.decode, BinaryPayload.balancedValue_eq]
  have hEq : BinaryPayload.value (fun j => bits.toArray.getD j false) 0 bits.length =
      BinaryPayload.value (fun j => bits.getD j false) 0 bits.length := by
    apply BinaryPayload.value_congr
    intro j
    by_cases hj : j < bits.length <;> simp [Array.getD, List.getD, hj]
  rw [hEq, littleValue_payload]

theorem value_reverse_decode (bits : List Bool) : value bits.reverse = BinaryPayload.decode bits := by
  rw [value_reverse, littleValue_decode]

def trim (bits : List Bool) : List Bool := bits.dropWhile (fun b => !b)

theorem value_trim (bits : List Bool) : value (trim bits) = value bits := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
    cases b
    · simpa only [trim, List.dropWhile_cons, Bool.not_false, ite_true, value_false_prefix] using ih
    · simp [trim]

theorem trim_length (bits : List Bool) : (trim bits).length ≤ bits.length := by
  exact List.Sublist.length_le (List.dropWhile_sublist (l := bits) (fun b => !b))

end Blotto.BinaryBigEndian
