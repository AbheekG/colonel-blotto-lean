import Blotto.BinaryEuclideanGCD

/-! A stored little-endian dimension is tested and decremented directly.
Numerical interpretation occurs in proof specifications. High zero padding
is accepted and retained; successful decrement never grows the payload. -/

namespace Blotto.BinaryStoredCountdown

def predecessor : List Bool → List Bool
  | [] => []
  | true :: rest => false :: rest
  | false :: rest => true :: predecessor rest

theorem predecessor_length (bits : List Bool) : (predecessor bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [predecessor,List.length_cons,ih]

theorem predecessor_value (bits : List Bool) (h : 0 < BinaryBigEndian.littleValue bits) :
    BinaryBigEndian.littleValue (predecessor bits) + 1 = BinaryBigEndian.littleValue bits := by
  induction bits with
  | nil => cases h
  | cons bit rest ih =>
      cases bit
      · have ht : 0 < BinaryBigEndian.littleValue rest := by
          change 0 < 2 * BinaryBigEndian.littleValue rest + 0 at h
          omega
        have hp := ih ht
        change 2 * BinaryBigEndian.littleValue (predecessor rest) + 1 + 1 = 2 * BinaryBigEndian.littleValue rest + 0
        omega
      · rfl

def predecessorVisits : List Bool → ℕ
  | [] => 1
  | true :: _ => 1
  | false :: rest => predecessorVisits rest + 1

theorem predecessorVisits_bound (bits : List Bool) : predecessorVisits bits ≤ bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [predecessorVisits,List.length_cons] <;> omega

def predecessorWithWork (bits : List Bool) : List Bool × ℕ :=
  (predecessor bits,4 * predecessorVisits bits)

theorem predecessorWithWork_state (bits : List Bool) : (predecessorWithWork bits).1 = predecessor bits := rfl

theorem predecessorWithWork_bound (bits : List Bool) : (predecessorWithWork bits).2 ≤ 4 * (bits.length + 1) :=
  Nat.mul_le_mul_left 4 (predecessorVisits_bound bits)

def nonzeroWithWork (bits : List Bool) : Bool × ℕ :=
  (BinaryEuclideanGCD.nonzero bits,bits.length + 1)

theorem nonzeroWithWork_value (bits : List Bool) : (nonzeroWithWork bits).1 = true ↔ 0 < BinaryBigEndian.littleValue bits :=
  BinaryEuclideanGCD.nonzero_true_iff bits

theorem nonzeroWithWork_false (bits : List Bool) (h : (nonzeroWithWork bits).1 = false) : BinaryBigEndian.littleValue bits = 0 := by
  have hz : ¬ 0 < BinaryBigEndian.littleValue bits := by
    intro hp
    have he := (nonzeroWithWork_value bits).mpr hp
    rw [h] at he
    cases he
  omega

end Blotto.BinaryStoredCountdown
