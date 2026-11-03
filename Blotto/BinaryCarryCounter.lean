import Blotto.BinaryBigEndianValue

/-! A little-endian Boolean carry counter. The counting loop performs no
natural-number arithmetic. A balanced decoder assembles only the final small
counter value; numerical recursion is a proof specification. -/

namespace Blotto.BinaryCarryCounter

def increment : List Bool → List Bool
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => false :: increment rest

def value (bits : List Bool) : ℕ := BinaryBigEndian.littleValue bits

theorem value_increment (bits : List Bool) : value (increment bits) = value bits + 1 := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
    cases b
    · simp [increment, value, BinaryBigEndian.littleValue]
    · change 2 * value (increment rest) = 2 * value rest + 1 + 1
      rw [ih]
      omega

def count {α : Type*} : List α → List Bool → List Bool
  | [], counter => counter
  | _ :: rest, counter => count rest (increment counter)

theorem count_value {α : Type*} (items : List α) (counter : List Bool) :
    value (count items counter) = value counter + items.length := by
  induction items generalizing counter with
  | nil => simp [count]
  | cons item rest ih =>
    rw [count, ih, value_increment]
    simp only [List.length_cons]
    omega

def lengthFromOne {α : Type*} (items : List α) : ℕ := BinaryPayload.decode (count items [true])

theorem lengthFromOne_eq {α : Type*} (items : List α) : lengthFromOne items = items.length + 1 := by
  rw [lengthFromOne, ← BinaryBigEndian.value_reverse_decode, BinaryBigEndian.value_reverse]
  change value (count items [true]) = _
  rw [count_value]
  change 1 + items.length = items.length + 1
  omega

def ones : List Bool → ℕ
  | [] => 0
  | false :: rest => ones rest
  | true :: rest => ones rest + 1

def carryCells : List Bool → ℕ
  | [] => 1
  | false :: _ => 1
  | true :: rest => carryCells rest + 1

theorem carryCells_pos (bits : List Bool) : 0 < carryCells bits := by
  induction bits with
  | nil => simp [carryCells]
  | cons bit rest ih => cases bit <;> simp only [carryCells] <;> omega

theorem carry_potential (bits : List Bool) : carryCells bits + ones (increment bits) = 2 + ones bits := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
    cases b
    · simp only [carryCells, ones, increment]
      omega
    · simp only [carryCells, ones, increment]
      omega

def countCarryCells {α : Type*} : List α → List Bool → ℕ
  | [], _ => 0
  | _ :: rest, counter => carryCells counter + countCarryCells rest (increment counter)

theorem countCarryCells_ge_length {α : Type*}
    (items : List α) (counter : List Bool) :
    items.length ≤ countCarryCells items counter := by
  induction items generalizing counter with
  | nil => rfl
  | cons item rest ih =>
      have hp := carryCells_pos counter
      have hr := ih (increment counter)
      simp only [List.length_cons,countCarryCells]
      omega

theorem count_potential {α : Type*} (items : List α) (counter : List Bool) :
    countCarryCells items counter + ones (count items counter) = 2 * items.length + ones counter := by
  induction items generalizing counter with
  | nil => simp [count, countCarryCells]
  | cons item rest ih =>
    have hCarry := carry_potential counter
    have hRest := ih (increment counter)
    simp only [count, countCarryCells, List.length_cons]
    omega

theorem countCarryCells_bound {α : Type*} (items : List α) (counter : List Bool) :
    countCarryCells items counter ≤ 2 * items.length + ones counter := by
  have h := count_potential items counter
  omega

theorem lengthFromOne_carry_bound {α : Type*} (items : List α) : countCarryCells items [true] ≤ 2 * items.length + 1 :=
  countCarryCells_bound items [true]

end Blotto.BinaryCarryCounter
