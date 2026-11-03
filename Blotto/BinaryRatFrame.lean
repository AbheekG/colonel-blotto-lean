import Blotto.BinaryNatFrame

/-! A portable rational frame stores a sign and two self-delimiting natural
frames. A zero denominator is rejected before rational division. Canonical
input/output rationals round-trip with every trailing suffix intact. -/

namespace Blotto.BinaryRatFrame

def signedValue (negative : Bool) (magnitude : ℕ) : ℚ :=
  if negative then -(magnitude : ℚ) else magnitude

def encode (q : ℚ) : List Bool :=
  decide (q.num < 0) :: (BinaryNatFrame.encode q.num.natAbs ++ BinaryNatFrame.encode q.den)

def read : List Bool → Option (ℚ × List Bool)
  | [] => none
  | negative :: bits =>
    (BinaryNatFrame.read bits).bind (fun first => (BinaryNatFrame.read first.2).bind (fun second =>
      if second.1 = 0 then none else some (signedValue negative first.1 / second.1, second.2)))

theorem signedValue_natAbs (z : ℤ) : signedValue (decide (z < 0)) z.natAbs = (z : ℚ) := by
  have hAbs : (z.natAbs : ℚ) = |(z : ℚ)| := by rw [Nat.cast_natAbs]; push_cast; rfl
  by_cases hz : z < 0
  · have hzQ : (z : ℚ) < 0 := by exact_mod_cast hz
    simp [signedValue, hz, hAbs, abs_of_neg hzQ]
  · have hzQ : (0 : ℚ) ≤ z := by exact_mod_cast le_of_not_gt hz
    simp [signedValue, hz, hAbs, abs_of_nonneg hzQ]

theorem encode_length (q : ℚ) : (encode q).length = 2 * rationalWordWidth q + 1 := by
  simp only [encode, List.length_cons, List.length_append, BinaryNatFrame.encode_length, rationalWordWidth]
  omega

theorem read_encode_append (q : ℚ) (suffix : List Bool) : read (encode q ++ suffix) = some (q, suffix) := by
  simp only [encode, List.cons_append, List.append_assoc, read,
    BinaryNatFrame.read_encode_append, Option.bind_some, ite_eq_right q.den_ne_zero,
    signedValue_natAbs, Rat.num_div_den]

theorem read_encode (q : ℚ) : read (encode q) = some (q, []) := by simpa using read_encode_append q []

theorem read_empty : read [] = none := rfl

theorem read_zero_denominator (negative : Bool) (magnitude : ℕ) (suffix : List Bool) :
    read (negative :: (BinaryNatFrame.encode magnitude ++ BinaryNatFrame.encode 0 ++ suffix)) = none := by
  simp only [read, List.append_assoc, BinaryNatFrame.read_encode_append, Option.bind_some, ite_true]

end Blotto.BinaryRatFrame
