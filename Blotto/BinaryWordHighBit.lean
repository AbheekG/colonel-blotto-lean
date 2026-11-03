import Blotto.BinaryBorrowProperties

/-! Dropping a known-zero high bit keeps an unsigned word's value. The runtime
uses paired list constructors and a tail accumulator, with no length integer. -/

namespace Blotto.BinaryWordHighBit

def reference : List Bool → List Bool
  | [] => []
  | [_] => []
  | a :: b :: rest => a :: reference (b :: rest)

def loop : List Bool → List Bool → List Bool
  | [], acc => acc.reverse
  | [_], acc => acc.reverse
  | a :: b :: rest, acc => loop (b :: rest) (a :: acc)

def drop (bits : List Bool) : List Bool := loop bits []

theorem loop_refines (bits acc : List Bool) : loop bits acc = acc.reverse ++ reference bits := by
  induction bits generalizing acc with
  | nil => simp [loop, reference]
  | cons bit rest ih =>
    cases rest with
    | nil => simp [loop, reference]
    | cons next tail =>
      rw [loop, ih]
      simp only [reference, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem drop_refines (bits : List Bool) : drop bits = reference bits := by
  rw [drop, loop_refines]
  simp

theorem reference_length (bits : List Bool) : (reference bits).length = bits.length - 1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    cases rest with
    | nil => rfl
    | cons next tail =>
      simp only [reference, List.length_cons] at ih ⊢
      omega

theorem drop_length (bits : List Bool) : (drop bits).length = bits.length - 1 := by
  rw [drop_refines]
  exact reference_length bits

theorem reference_value (bits : List Bool)
    (h : BinaryBigEndian.littleValue bits < 2 ^ (bits.length - 1)) :
    BinaryBigEndian.littleValue (reference bits) = BinaryBigEndian.littleValue bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    cases rest with
    | nil =>
      cases bit
      · rfl
      · norm_num [BinaryBigEndian.littleValue] at h
    | cons next tail =>
      have ht : BinaryBigEndian.littleValue (next :: tail) < 2 ^ tail.length := by
        simp only [List.length_cons, Nat.add_sub_cancel] at h
        change 2 * BinaryBigEndian.littleValue (next :: tail) + (if bit then 1 else 0) < 2 ^ (tail.length + 1) at h
        rw [pow_succ] at h
        omega
      have hv := ih (by simpa only [List.length_cons, Nat.add_sub_cancel] using ht)
      change 2 * BinaryBigEndian.littleValue (reference (next :: tail)) + (if bit then 1 else 0) =
        2 * BinaryBigEndian.littleValue (next :: tail) + (if bit then 1 else 0)
      rw [hv]

theorem drop_value (bits : List Bool)
    (h : BinaryBigEndian.littleValue bits < 2 ^ (bits.length - 1)) :
    BinaryBigEndian.littleValue (drop bits) = BinaryBigEndian.littleValue bits := by
  rw [drop_refines]
  exact reference_value bits h

theorem littleValue_append (a b : List Bool) :
    BinaryBigEndian.littleValue (a ++ b) = BinaryBigEndian.littleValue a + 2 ^ a.length * BinaryBigEndian.littleValue b := by
  induction a with
  | nil => simp [BinaryBigEndian.littleValue]
  | cons bit rest ih =>
    simp only [List.cons_append, BinaryBigEndian.littleValue, List.length_cons, pow_succ, ih]
    ring

theorem pad_value (bits : List Bool) : BinaryBigEndian.littleValue (bits ++ [false]) = BinaryBigEndian.littleValue bits := by
  rw [littleValue_append]
  simp [BinaryBigEndian.littleValue]

def visits : List Bool → ℕ
  | [] | [_] => 1
  | _ :: b :: rest => 1 + visits (b :: rest)

theorem visits_bound (bits : List Bool) : visits bits ≤ bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    cases rest with
    | nil => simp [visits]
    | cons next tail =>
      simp only [visits, List.length_cons] at ih ⊢
      omega

end Blotto.BinaryWordHighBit
