import Blotto.BinaryNatFrame
import Blotto.BinaryAccuracyInput

/-! Positive raw accuracy words are framed without fraction reduction.
Readback retains the exact numerator/denominator and the established precision. -/

namespace Blotto.BinaryAccuracyFrame

def encode (a : BinaryAccuracyInput) : List Bool := BinaryNatFrame.encode a.numerator ++ BinaryNatFrame.encode a.denominator

def read (bits : List Bool) : Option (BinaryAccuracyInput × List Bool) :=
  (BinaryNatFrame.read bits).bind (fun first => (BinaryNatFrame.read first.2).bind (fun second =>
    if h : 0 < first.1 ∧ 0 < second.1 then some (⟨first.1, second.1, h.1, h.2⟩, second.2) else none))

theorem read_encode_append (a : BinaryAccuracyInput) (suffix : List Bool) : read (encode a ++ suffix) = some (a, suffix) := by
  simp only [read, encode, List.append_assoc, BinaryNatFrame.read_encode_append, Option.bind_some]
  rw [dite_eq_left (show 0 < a.numerator ∧ 0 < a.denominator from ⟨a.numerator_pos, a.denominator_pos⟩)]

theorem encode_length (a : BinaryAccuracyInput) :
    (encode a).length = 2 * (binaryWordWidth a.numerator + binaryWordWidth a.denominator) + 2 := by
  simp only [encode, List.length_append, BinaryNatFrame.encode_length]
  omega

theorem read_zero_numerator (denominator : ℕ) (suffix : List Bool) :
    read (BinaryNatFrame.encode 0 ++ BinaryNatFrame.encode denominator ++ suffix) = none := by
  simp only [read, List.append_assoc, BinaryNatFrame.read_encode_append, Option.bind_some, Nat.lt_irrefl,
    false_and, dite_false]

theorem read_zero_denominator (numerator : ℕ) (suffix : List Bool) :
    read (BinaryNatFrame.encode numerator ++ BinaryNatFrame.encode 0 ++ suffix) = none := by
  simp only [read, List.append_assoc, BinaryNatFrame.read_encode_append, Option.bind_some, Nat.lt_irrefl,
    and_false, dite_false]

end Blotto.BinaryAccuracyFrame
