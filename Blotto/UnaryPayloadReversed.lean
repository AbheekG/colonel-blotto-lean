import Blotto.UnaryPayload

/-! The paired cursor can return its accumulated reversed payload directly.
The positive-word reader consumes this big-endian order without two reversals. -/

namespace Blotto.UnaryPayload

def consumeReversed : List Bool → List Bool → List Bool → Option (List Bool × List Bool)
  | [], _, _ => none
  | true :: _, payload, reversed => some (reversed, payload)
  | false :: _, [], _ => none
  | false :: ruler, b :: payload, reversed => consumeReversed ruler payload (b :: reversed)

def readReversed (frame : List Bool) : Option (List Bool × List Bool) :=
  (findPayload frame).bind (fun payload => consumeReversed frame payload [])

theorem consumeReversed_refines (ruler payload reversed : List Bool) :
    consumeReversed ruler payload reversed = (consume ruler payload reversed).map (fun pair => (pair.1.reverse, pair.2)) := by
  induction ruler generalizing payload reversed with
  | nil => rfl
  | cons b ruler ih =>
    cases b
    · cases payload with
      | nil => rfl
      | cons bit payload => exact ih payload (bit :: reversed)
    · simp [consumeReversed, consume]

theorem readReversed_refines (frame : List Bool) :
    readReversed frame = (read frame).map (fun pair => (pair.1.reverse, pair.2)) := by
  unfold readReversed read
  cases hs : findPayload frame with
  | none => rfl
  | some payload => exact consumeReversed_refines frame payload []

end Blotto.UnaryPayload
