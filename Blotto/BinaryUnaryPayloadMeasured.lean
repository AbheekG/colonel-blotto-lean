import Blotto.BinaryUnaryPayloadLifetime
import Blotto.BinarySeedCursorMeasured

/-! The actual delimiter search, bounded payload copy and reversal return
their old data/trace together with source work. No decoded width or second
reader is executed. Work and trace are ghost instruments: their native
evaluation, reference-bit transport and allocator costs remain separate. -/
namespace Blotto.BinaryUnaryPayloadMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def find : List Bool → (Option (List Bool) × Trace) × ℕ
  | [] => ((none,wrap 8 1 []),4)
  | true::rest => ((some rest,wrap 8 1 []),4)
  | false::rest =>
      let later := find rest
      ((later.1.1,wrap 8 1 [later.1.2]),later.2+4)

theorem find_erases (frame : List Bool) :
    (find frame).1 = BinaryUnaryPayloadLifetime.findWithTrace frame := by
  induction frame with
  | nil => rfl
  | cons bit rest ih => cases bit <;>
      simp only [find,BinaryUnaryPayloadLifetime.findWithTrace,ih]

theorem find_work (frame : List Bool) : (find frame).2 ≤ 4*(frame.length+1) := by
  induction frame with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [find,List.length_cons] <;> omega

def consume : List Bool → List Bool → List Bool → (Option (List Bool × List Bool) × Trace) × ℕ
  | [],_,_ => ((none,wrap 8 1 []),4)
  | true::_,payload,reversed => ((some (reversed,payload),wrap 8 1 []),4)
  | false::_,[],_ => ((none,wrap 8 1 []),4)
  | false::ruler,bit::payload,reversed =>
      let later := consume ruler payload (bit::reversed)
      ((later.1.1,wrapList 1 8 1 [later.1.2]),later.2+4)

theorem consume_erases (ruler payload reversed : List Bool) :
    (consume ruler payload reversed).1 =
      BinaryUnaryPayloadLifetime.consumeReversedWithTrace ruler payload reversed := by
  induction ruler generalizing payload reversed with
  | nil => rfl
  | cons mark ruler ih =>
      cases mark
      · cases payload with
        | nil => rfl
        | cons bit payload => simp only [consume,
            BinaryUnaryPayloadLifetime.consumeReversedWithTrace,ih]
      · rfl

theorem consume_work (ruler payload reversed : List Bool) :
    (consume ruler payload reversed).2 ≤ 4*(ruler.length+1) := by
  induction ruler generalizing payload reversed with
  | nil => rfl
  | cons mark ruler ih =>
      cases mark
      · cases payload with
        | nil => simp only [consume,List.length_cons]; omega
        | cons bit payload =>
            have h := ih payload (bit::reversed)
            simp only [consume,List.length_cons]
            omega
      · simp only [consume,List.length_cons]; omega

def readReversed (frame : List Bool) : (Option (List Bool × List Bool) × Trace) × ℕ :=
  let found := find frame
  match found.1.1 with
  | none => ((none,wrap 16 2 [found.1.2]),found.2+4)
  | some payload =>
      let copied := consume frame payload []
      ((copied.1.1,wrap 24 2 [found.1.2,copied.1.2]),found.2+copied.2+8)

theorem readReversed_erases (frame : List Bool) :
    (readReversed frame).1 = BinaryUnaryPayloadLifetime.readReversedWithTrace frame := by
  unfold readReversed BinaryUnaryPayloadLifetime.readReversedWithTrace
  dsimp only
  simp only [find_erases,consume_erases]
  cases (BinaryUnaryPayloadLifetime.findWithTrace frame).1 <;> rfl

theorem readReversed_work (frame : List Bool) : (readReversed frame).2 ≤ 16*(frame.length+1) := by
  have hf := find_work frame
  unfold readReversed
  dsimp only
  split
  · omega
  · rename_i payload hSome
    have hc := consume_work frame payload []
    omega

def read (frame : List Bool) : (Option (List Bool × List Bool) × Trace) × ℕ :=
  let raw := readReversed frame
  match raw.1.1 with
  | none => ((none,wrap 16 2 [raw.1.2]),raw.2+4)
  | some parsed =>
      let reversed := BinarySeedCursorMeasured.reverse parsed.1 []
      ((some (reversed.1.1,parsed.2),wrap 24 2 [raw.1.2,reversed.1.2]),raw.2+reversed.2+8)

theorem read_erases (frame : List Bool) :
    (read frame).1 = BinaryUnaryPayloadLifetime.readWithTrace frame := by
  unfold read BinaryUnaryPayloadLifetime.readWithTrace
  dsimp only
  simp only [readReversed_erases,BinarySeedCursorMeasured.reverse_erases]
  cases (BinaryUnaryPayloadLifetime.readReversedWithTrace frame).1 <;> rfl

theorem read_work (frame : List Bool) : (read frame).2 ≤ 32*(frame.length+1) := by
  have hr := readReversed_work frame
  unfold read
  dsimp only
  split
  · omega
  · rename_i parsed hSome
    have hLength := BinaryUnaryPayloadLifetime.readReversed_payload_length frame parsed
      ((congrArg Prod.fst (readReversed_erases frame)).symm.trans hSome)
    have hb := BinarySeedCursorMeasured.reverse_work parsed.1 []
    rw [BinaryMidpointTapeLifetime.reverse_work] at hb
    omega

theorem read_payload_length (frame : List Bool) (parsed : List Bool × List Bool)
    (h : (read frame).1.1 = some parsed) : parsed.1.length ≤ frame.length :=
  BinaryUnaryPayloadLifetime.read_payload_length frame parsed
    ((congrArg Prod.fst (read_erases frame)).symm.trans h)

theorem read_suffix_lt (frame : List Bool) (parsed : List Bool × List Bool)
    (h : (read frame).1.1 = some parsed) : parsed.2.length < frame.length :=
  BinaryUnaryPayloadLifetime.read_suffix_lt frame parsed
    ((congrArg Prod.fst (read_erases frame)).symm.trans h)

theorem read_usage (frame : List Bool) : usage (read frame).1.2 ≤ 128*(frame.length+1) := by
  rw [read_erases]
  exact BinaryUnaryPayloadLifetime.readWithTrace_usage frame

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (read frame).1.2 steps ≤ borrowed+frame.length+128*(frame.length+1) ∧
    framePeak ((read frame).1.2.take steps) ≤ 128*(frame.length+1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (read_usage frame) _ steps

end Blotto.BinaryUnaryPayloadMeasured
