import Blotto.BinaryPRGAccuracyRulerRequest

/-! A seed cursor consumes one bit per Boolean ruler cell, using shared
suffixes and a reversed accumulator. No seed-length integer is assembled by
its runtime. Exact block/suffix semantics and reached Boolean/cell visits
include too-short rejection. Scalar/address/physical costs are separate. -/

namespace Blotto.BinarySeedCursor

def loop : List Bool → List Bool → List Bool → Option (List Bool × List Bool)
  | [], bits, reversed => some (reversed.reverse,bits)
  | _ :: _, [], _ => none
  | _ :: ruler, bit :: bits, reversed => loop ruler bits (bit :: reversed)

theorem loop_state (ruler bits reversed : List Bool) : loop ruler bits reversed =
    if ruler.length ≤ bits.length then some (reversed.reverse ++ bits.take ruler.length,bits.drop ruler.length) else none := by
  induction ruler generalizing bits reversed with
  | nil => simp [loop]
  | cons cell ruler ih =>
      cases bits with
      | nil => simp [loop]
      | cons bit bits =>
          rw [loop,ih]
          simp only [List.length_cons,Nat.add_le_add_iff_right,List.take_succ_cons,List.drop_succ_cons,
            List.reverse_cons,List.append_assoc,List.singleton_append]

def visits : List Bool → List Bool → ℕ
  | [], _ => 1
  | _ :: _, [] => 1
  | _ :: ruler, _ :: bits => visits ruler bits + 1

theorem visits_bound (ruler bits : List Bool) : visits ruler bits ≤ ruler.length + 1 := by
  induction ruler generalizing bits with
  | nil => rfl
  | cons cell ruler ih =>
      cases bits with
      | nil => simp only [visits,List.length_cons]; omega
      | cons bit bits => have ht := ih bits; simp only [visits,List.length_cons]; omega

def consume (ruler bits : List Bool) : Option (List Bool × List Bool) × ℕ :=
  (loop ruler bits [],5 * visits ruler bits)

theorem consume_state (ruler bits : List Bool) : (consume ruler bits).1 =
    if ruler.length ≤ bits.length then some (bits.take ruler.length,bits.drop ruler.length) else none := by
  rw [consume,loop_state]
  simp only [List.reverse_nil,List.nil_append]

theorem consume_bound (ruler bits : List Bool) : (consume ruler bits).2 ≤ 5 * (ruler.length + 1) :=
  Nat.mul_le_mul_left 5 (visits_bound ruler bits)

theorem consume_success (ruler bits block suffix : List Bool)
    (h : (consume ruler bits).1 = some (block,suffix)) : block.length = ruler.length ∧ bits = block ++ suffix := by
  rw [consume_state] at h
  split at h
  · rename_i hEnough
    cases Option.some.inj h
    constructor
    · simp only [List.length_take,Nat.min_eq_left hEnough]
    · exact (List.take_append_drop ruler.length bits).symm
  · cases h

theorem consume_append (ruler block suffix : List Bool) (h : block.length = ruler.length) :
    (consume ruler (block ++ suffix)).1 = some (block,suffix) := by
  rw [consume_state]
  have hEnough : ruler.length ≤ (block ++ suffix).length := by simp only [List.length_append,h]; omega
  rw [ite_eq_left hEnough,← h,List.take_left,List.drop_left]

end Blotto.BinarySeedCursor
