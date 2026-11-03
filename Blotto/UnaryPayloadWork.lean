import Blotto.UnaryPayloadReversed

/-! Paired-cursor visits and payload cons cells are linear in the frame.
The runtime uses Boolean cells and shared suffixes rather than a numeric width
counter. Physical cell/allocator and subsequent word-width costs are separate. -/

namespace Blotto.UnaryPayload

def findSteps : List Bool → ℕ
  | [] => 1
  | true :: _ => 1
  | false :: rest => findSteps rest + 1

def consumeCopies : List Bool → List Bool → ℕ
  | [], _ => 0
  | true :: _, _ => 0
  | false :: _, [] => 0
  | false :: ruler, _ :: payload => consumeCopies ruler payload + 1

def readSteps (frame : List Bool) : ℕ := findSteps frame +
  match findPayload frame with
  | none => 0
  | some payload => consumeCopies frame payload + 1

theorem findSteps_bound (frame : List Bool) : findSteps frame ≤ frame.length + 1 := by
  induction frame with
  | nil => rfl
  | cons b rest ih => cases b <;> simp only [findSteps, List.length_cons] <;> omega

theorem findSteps_suffix (frame payload : List Bool) (h : findPayload frame = some payload) :
    findSteps frame + payload.length = frame.length := by
  induction frame with
  | nil => cases h
  | cons b rest ih =>
    cases b
    · have ht := ih h
      simp only [findSteps, List.length_cons]
      omega
    · cases Option.some.inj h
      simp only [findSteps, List.length_cons]
      omega

theorem consumeCopies_bound (ruler payload : List Bool) : consumeCopies ruler payload ≤ payload.length := by
  induction ruler generalizing payload with
  | nil => simp [consumeCopies]
  | cons b ruler ih =>
    cases b
    · cases payload with
      | nil => rfl
      | cons bit payload => exact Nat.add_le_add_right (ih payload) 1
    · exact Nat.zero_le _

theorem consumeCopies_ruler_bound (ruler payload : List Bool) : consumeCopies ruler payload ≤ ruler.length := by
  induction ruler generalizing payload with
  | nil => rfl
  | cons b ruler ih =>
    cases b
    · cases payload with
      | nil => exact Nat.zero_le _
      | cons bit payload => exact Nat.add_le_add_right (ih payload) 1
    · exact Nat.zero_le _

theorem readSteps_bound (frame : List Bool) : readSteps frame ≤ frame.length + 1 := by
  unfold readSteps
  cases h : findPayload frame with
  | none => simpa only [Nat.add_zero] using findSteps_bound frame
  | some payload =>
    have hs := findSteps_suffix frame payload h
    have hc := consumeCopies_bound frame payload
    change findSteps frame + (consumeCopies frame payload + 1) ≤ frame.length + 1
    calc
      _ = (findSteps frame + consumeCopies frame payload) + 1 := (Nat.add_assoc _ _ _).symm
      _ ≤ (findSteps frame + payload.length) + 1 := Nat.add_le_add_right (Nat.add_le_add_left hc _) 1
      _ = frame.length + 1 := by rw [hs]

theorem consumeReversed_prefix (width : ℕ) (tail payload reversed : List Bool) :
    consumeReversed (List.replicate width false ++ true :: tail) payload reversed =
      if width ≤ payload.length then some ((payload.take width).reverse ++ reversed, payload.drop width) else none := by
  rw [consumeReversed_refines, consume_prefix]
  split
  · simp [List.reverse_append]
  · rfl

theorem consumeCopies_prefix (width : ℕ) (tail payload : List Bool) :
    consumeCopies (List.replicate width false ++ true :: tail) payload = min width payload.length := by
  induction width generalizing payload with
  | zero => simp [consumeCopies]
  | succ width ih =>
    cases payload with
    | nil => simp [consumeCopies, List.replicate_succ]
    | cons b payload =>
      simp only [List.replicate_succ, List.cons_append, consumeCopies, ih, List.length_cons]
      omega

end Blotto.UnaryPayload
