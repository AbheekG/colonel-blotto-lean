import Blotto.BinaryNatFrame

/-! Width prefixes themselves serve as a unary ruler. Two list cursors
extract the payload without assembling a width integer or copying its prefix. -/

namespace Blotto.UnaryPayload

def findPayload : List Bool → Option (List Bool)
  | [] => none
  | true :: rest => some rest
  | false :: rest => findPayload rest

def consume : List Bool → List Bool → List Bool → Option (List Bool × List Bool)
  | [], _, _ => none
  | true :: _, payload, reversed => some (reversed.reverse, payload)
  | false :: _, [], _ => none
  | false :: ruler, b :: payload, reversed => consume ruler payload (b :: reversed)

def read (frame : List Bool) : Option (List Bool × List Bool) :=
  (findPayload frame).bind (fun payload => consume frame payload [])

theorem findPayload_scanWidth (count : ℕ) (frame : List Bool) :
    findPayload frame = (BinaryNatFrame.scanWidth count frame).map Prod.snd := by
  induction frame generalizing count with
  | nil => rfl
  | cons b rest ih => cases b; exact ih (count + 1); rfl

theorem scanWidth_shape (count : ℕ) (frame : List Bool) (width : ℕ) (rest : List Bool)
    (h : BinaryNatFrame.scanWidth count frame = some (width, rest)) :
    ∃ marks, frame = List.replicate marks false ++ true :: rest ∧ width = count + marks := by
  induction frame generalizing count with
  | nil => cases h
  | cons b tail ih =>
    cases b
    · rcases ih (count + 1) h with ⟨marks, hFrame, hWidth⟩
      refine ⟨marks + 1, ?_, ?_⟩
      · simp only [List.replicate_succ, List.cons_append, hFrame]
      · omega
    · cases Option.some.inj h
      exact ⟨0, rfl, by omega⟩

theorem consume_prefix (width : ℕ) (tail payload reversed : List Bool) :
    consume (List.replicate width false ++ true :: tail) payload reversed =
      if width ≤ payload.length then some (reversed.reverse ++ payload.take width, payload.drop width) else none := by
  induction width generalizing payload reversed with
  | zero => simp [consume]
  | succ width ih =>
    cases payload with
    | nil => simp [List.replicate_succ, consume]
    | cons b payload =>
      rw [List.replicate_succ]
      simp only [List.cons_append, consume]
      rw [ih]
      simp only [List.length_cons, Nat.succ_le_succ_iff, List.take_succ_cons, List.drop_succ_cons,
        List.reverse_cons, List.append_assoc, List.singleton_append]

theorem read_refines (frame : List Bool) :
    read frame = (BinaryNatFrame.scanWidth 0 frame).bind (fun pair =>
      if pair.1 ≤ pair.2.length then some (pair.2.take pair.1, pair.2.drop pair.1) else none) := by
  rw [read, findPayload_scanWidth 0]
  cases hs : BinaryNatFrame.scanWidth 0 frame with
  | none => rfl
  | some pair =>
    rcases pair with ⟨width, payload⟩
    rcases scanWidth_shape 0 frame width payload hs with ⟨marks, hFrame, hWidth⟩
    have hp : marks = width := by omega
    subst marks
    dsimp only [Option.map_some, Option.bind_some]
    rw [hFrame, consume_prefix]
    simp only [List.reverse_nil, List.nil_append]

end Blotto.UnaryPayload
