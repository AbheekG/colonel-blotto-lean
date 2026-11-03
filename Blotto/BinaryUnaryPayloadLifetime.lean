import Blotto.BinaryCanonicalFrameWork
import Blotto.BinaryPRGHeapTraceUsage

/-! Actual paired Boolean cursors locate the delimiter and copy only the
reached payload. No numeric width/count or old reader is executed alongside
the trace. Incoming frame and shared suffixes stay borrowed; all allocated
accumulator/reversal cells and source activations remain retained. -/
namespace Blotto.BinaryUnaryPayloadLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def findWithTrace : List Bool → Option (List Bool) × Trace
  | [] => (none,wrap 8 1 [])
  | true::rest => (some rest,wrap 8 1 [])
  | false::rest =>
      let later := findWithTrace rest
      (later.1,wrap 8 1 [later.2])

theorem findWithTrace_state (frame : List Bool) :
    (findWithTrace frame).1 = UnaryPayload.findPayload frame := by
  induction frame with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [findWithTrace,UnaryPayload.findPayload,ih]

theorem findWithTrace_usage (frame : List Bool) : usage (findWithTrace frame).2 ≤ 16*(frame.length+1) := by
  induction frame with
  | nil => exact (wrap_usage 8 1 []).trans (by simp <;> omega)
  | cons bit rest ih =>
      cases bit
      · have h := wrap_usage 8 1 [(findWithTrace rest).2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at h
        change usage (wrap 8 1 [(findWithTrace rest).2]) ≤ _
        simp only [List.length_cons]
        omega
      · exact (wrap_usage 8 1 []).trans (by simp <;> omega)

def consumeReversedWithTrace : List Bool → List Bool → List Bool → Option (List Bool × List Bool) × Trace
  | [], _, _ => (none,wrap 8 1 [])
  | true::_, payload, reversed => (some (reversed,payload),wrap 8 1 [])
  | false::_, [], _ => (none,wrap 8 1 [])
  | false::ruler, bit::payload, reversed =>
      let later := consumeReversedWithTrace ruler payload (bit::reversed)
      (later.1,wrapList 1 8 1 [later.2])

theorem consumeReversedWithTrace_state (ruler payload reversed : List Bool) :
    (consumeReversedWithTrace ruler payload reversed).1 = UnaryPayload.consumeReversed ruler payload reversed := by
  induction ruler generalizing payload reversed with
  | nil => rfl
  | cons mark ruler ih =>
      cases mark
      · cases payload with
        | nil => rfl
        | cons bit payload => exact ih payload (bit::reversed)
      · rfl

theorem consumeReversedWithTrace_usage (ruler payload reversed : List Bool) :
    usage (consumeReversedWithTrace ruler payload reversed).2 ≤ 16*(ruler.length+1) := by
  induction ruler generalizing payload reversed with
  | nil => exact (wrap_usage 8 1 []).trans (by simp <;> omega)
  | cons mark ruler ih =>
      cases mark
      · cases payload with
        | nil => exact (wrap_usage 8 1 []).trans (by simp <;> omega)
        | cons bit payload =>
            have h := wrapList_usage 1 8 1 [(consumeReversedWithTrace ruler payload (bit::reversed)).2]
            have ht := ih payload (bit::reversed)
            simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at h
            change usage (wrapList 1 8 1 [(consumeReversedWithTrace ruler payload (bit::reversed)).2]) ≤ _
            simp only [List.length_cons]
            omega
      · exact (wrap_usage 8 1 []).trans (by simp <;> omega)

def readReversedWithTrace (frame : List Bool) : Option (List Bool × List Bool) × Trace :=
  let found := findWithTrace frame
  match found.1 with
  | none => (none,wrap 16 2 [found.2])
  | some payload =>
      let copied := consumeReversedWithTrace frame payload []
      (copied.1,wrap 24 2 [found.2,copied.2])

theorem readReversedWithTrace_state (frame : List Bool) :
    (readReversedWithTrace frame).1 = UnaryPayload.readReversed frame := by
  unfold readReversedWithTrace UnaryPayload.readReversed
  dsimp only
  rw [findWithTrace_state]
  cases UnaryPayload.findPayload frame with
  | none => rfl
  | some payload => exact consumeReversedWithTrace_state frame payload []

theorem readReversedWithTrace_usage (frame : List Bool) : usage (readReversedWithTrace frame).2 ≤ 64*(frame.length+1) := by
  have hFind := findWithTrace_usage frame
  unfold readReversedWithTrace
  dsimp only
  split
  · have h := wrap_usage 16 2 [(findWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at h
    change usage (wrap 16 2 [(findWithTrace frame).2]) ≤ _
    omega
  · rename_i payload hSome
    have hCopy := consumeReversedWithTrace_usage frame payload []
    have h := wrap_usage 24 2 [(findWithTrace frame).2,(consumeReversedWithTrace frame payload []).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at h
    change usage (wrap 24 2 [(findWithTrace frame).2,(consumeReversedWithTrace frame payload []).2]) ≤ _
    omega

theorem readReversed_payload_length (frame : List Bool) (parsed : List Bool × List Bool)
    (h : (readReversedWithTrace frame).1 = some parsed) : parsed.1.length ≤ frame.length := by
  rw [readReversedWithTrace_state,UnaryPayload.readReversed_refines] at h
  obtain ⟨raw,hRaw,hOut⟩ := Option.map_eq_some_iff.mp h
  subst parsed
  rw [List.length_reverse]
  exact BinaryPRGHeaderFrame.readPayload_length_bound frame raw.1 raw.2 hRaw

def readWithTrace (frame : List Bool) : Option (List Bool × List Bool) × Trace :=
  let raw := readReversedWithTrace frame
  match raw.1 with
  | none => (none,wrap 16 2 [raw.2])
  | some parsed =>
      let reversed := BinarySeedPreparationSpace.reverseWithTrace parsed.1 []
      (some (reversed.1,parsed.2),wrap 24 2 [raw.2,reversed.2])

theorem readWithTrace_state (frame : List Bool) : (readWithTrace frame).1 = PositiveBinaryWord.readPayload frame := by
  have h : (readWithTrace frame).1 = (UnaryPayload.readReversed frame).map (fun pair => (pair.1.reverse,pair.2)) := by
    unfold readWithTrace
    dsimp only
    rw [readReversedWithTrace_state]
    cases UnaryPayload.readReversed frame with
    | none => rfl
    | some parsed => simp only [Option.map_some,BinarySeedPreparationSpace.reverseWithTrace_result,List.reverseAux_eq,List.append_nil]
  rw [h,UnaryPayload.readReversed_refines,Option.map_map]
  simp only [Function.comp_def,List.reverse_reverse]
  change (UnaryPayload.read frame).map (fun x => (x.1,x.2)) = UnaryPayload.read frame
  cases UnaryPayload.read frame <;> rfl

theorem readWithTrace_usage (frame : List Bool) : usage (readWithTrace frame).2 ≤ 128*(frame.length+1) := by
  have hRaw := readReversedWithTrace_usage frame
  unfold readWithTrace
  dsimp only
  split
  · have h := wrap_usage 16 2 [(readReversedWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at h
    change usage (wrap 16 2 [(readReversedWithTrace frame).2]) ≤ _
    omega
  · rename_i parsed hSome
    have hLength := readReversed_payload_length frame parsed hSome
    have hCells := reverseWithTrace_cells parsed.1 []
    have hArrays := reverseWithTrace_arrays parsed.1 []
    have hFrames := reverseWithTrace_frames parsed.1 []
    have hRev : usage (reverseWithTrace parsed.1 []).2 ≤ 2*frame.length+1 := by
      unfold usage BinaryPRGHeapPrimitiveLifetime.cells
      omega
    have h := wrap_usage 24 2 [(readReversedWithTrace frame).2,(reverseWithTrace parsed.1 []).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at h
    change usage (wrap 24 2 [(readReversedWithTrace frame).2,(reverseWithTrace parsed.1 []).2]) ≤ _
    omega

theorem read_payload_length (frame : List Bool) (parsed : List Bool × List Bool)
    (h : (readWithTrace frame).1 = some parsed) : parsed.1.length ≤ frame.length :=
  BinaryPRGHeaderFrame.readPayload_length_bound frame parsed.1 parsed.2 ((readWithTrace_state frame).symm.trans h)

theorem read_suffix_lt (frame : List Bool) (parsed : List Bool × List Bool)
    (h : (readWithTrace frame).1 = some parsed) : parsed.2.length < frame.length :=
  BinaryCanonicalFrameWork.payload_suffix_lt frame parsed.1 parsed.2 ((readWithTrace_state frame).symm.trans h)

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (readWithTrace frame).2 steps ≤ borrowed+frame.length+128*(frame.length+1) ∧
    framePeak ((readWithTrace frame).2.take steps) ≤ 128*(frame.length+1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (readWithTrace_usage frame) _ steps

end Blotto.BinaryUnaryPayloadLifetime
