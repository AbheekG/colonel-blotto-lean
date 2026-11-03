import Blotto.BinaryMidpointTapeLifetime

/-! Actual measured Boolean/list cursor: structural ruler consumption and
accumulator reversal, including premature EOF. Work instruments are ghost;
no numeric countdown, reader-price premise or width oracle is used. -/
namespace Blotto.BinarySeedCursorWork

def loopWithWork : List Bool → List Bool → List Bool → Option (List Bool × List Bool) × ℕ
  | [],bits,reversed =>
      let back := BinaryMidpointTapeLifetime.reverseWithWork reversed []
      (some (back.1,bits),back.2+2)
  | _::_,[],_ => (none,2)
  | _::ruler,bit::bits,reversed =>
      let later := loopWithWork ruler bits (bit::reversed)
      (later.1,later.2+4)

theorem loop_state (ruler bits reversed : List Bool) :
    (loopWithWork ruler bits reversed).1 = BinarySeedCursor.loop ruler bits reversed := by
  induction ruler generalizing bits reversed with
  | nil => simp only [loopWithWork,BinaryMidpointTapeLifetime.reverse_work_state,
      BinarySeedCursor.loop,List.reverseAux_eq,List.append_nil]
  | cons cell ruler ih => cases bits with
    | nil => rfl
    | cons bit bits => exact ih bits (bit::reversed)

theorem loop_work (ruler bits reversed : List Bool) :
    (loopWithWork ruler bits reversed).2 ≤ 8*ruler.length+4*reversed.length+4 := by
  induction ruler generalizing bits reversed with
  | nil => simp only [loopWithWork,BinaryMidpointTapeLifetime.reverse_work,List.length_nil]; omega
  | cons cell ruler ih => cases bits with
    | nil => simp only [loopWithWork,List.length_cons]; omega
    | cons bit bits =>
      have h := ih bits (bit::reversed)
      simp only [loopWithWork,List.length_cons] at h ⊢
      omega

def consumeWithWork (ruler bits : List Bool) : Option (List Bool × List Bool) × ℕ := loopWithWork ruler bits []

theorem consume_state (ruler bits : List Bool) :
    (consumeWithWork ruler bits).1 = (BinarySeedCursor.consume ruler bits).1 := loop_state ruler bits []

theorem consume_trace (ruler bits : List Bool) :
    (consumeWithWork ruler bits).1 = (BinarySeedPreparationSpace.consumeWithTrace ruler bits).1.1 := by
  rw [consume_state,BinarySeedPreparationSpace.consumeWithTrace_option]

theorem consume_work (ruler bits : List Bool) : (consumeWithWork ruler bits).2 ≤ 8*ruler.length+4 := by
  simpa only [consumeWithWork,List.length_nil,Nat.mul_zero,Nat.add_zero] using loop_work ruler bits []

end Blotto.BinarySeedCursorWork
