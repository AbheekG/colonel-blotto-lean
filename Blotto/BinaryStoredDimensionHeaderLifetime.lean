import Blotto.BinaryStoredDimensionHeader
import Blotto.BinaryUnaryPayloadLifetime

/-! The dimension remains a Boolean payload. Actual reverse/trim/reverse
work returns both the canonical payload and the old header visit metadata,
so producing retained header bytes does not replay a trim/decoder. Exact
old header fields and every rejection/suffix are preserved. -/
namespace Blotto.BinaryStoredDimensionHeaderLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def dropWithTrace : List Bool → (List Bool × ℕ) × Trace
  | [] => (([],1),wrap 8 1 [])
  | true::rest => ((true::rest,1),wrapList 1 8 1 [])
  | false::rest =>
      let later := dropWithTrace rest
      ((later.1.1,later.1.2+1),wrap 8 1 [later.2])

theorem dropWithTrace_state (bits : List Bool) :
    (dropWithTrace bits).1 = (BinaryBigEndian.trim bits,BinaryCanonicalMagnitude.scanVisits bits) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp [dropWithTrace,BinaryBigEndian.trim,BinaryCanonicalMagnitude.scanVisits,ih,Nat.add_comm]

theorem dropWithTrace_usage (bits : List Bool) : usage (dropWithTrace bits).2 ≤ 16*(bits.length+1) := by
  induction bits with
  | nil => exact (wrap_usage 8 1 []).trans (by simp)
  | cons bit rest ih =>
      cases bit
      · have hw := wrap_usage 8 1 [(dropWithTrace rest).2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
        change usage (wrap 8 1 [(dropWithTrace rest).2]) ≤ _
        simp only [List.length_cons]
        omega
      · exact (wrapList_usage 1 8 1 []).trans (by simp <;> omega)

def trimWithTrace (bits : List Bool) : (List Bool × ℕ) × Trace :=
  let front := BinarySeedPreparationSpace.reverseWithTrace bits []
  let dropped := dropWithTrace front.1
  let back := BinarySeedPreparationSpace.reverseWithTrace dropped.1.1 []
  let work := 2*bits.length+3*dropped.1.2+2*back.1.length+2
  ((back.1,work),wrap 32 (2*bits.length+4) [front.2,dropped.2,back.2])

theorem trimWithTrace_state (bits : List Bool) :
    (trimWithTrace bits).1 = (BinaryCanonicalMagnitude.trim bits,BinaryCanonicalMagnitude.bitWork bits) := by
  simp only [trimWithTrace,BinarySeedPreparationSpace.reverseWithTrace_result,List.reverseAux_eq,List.append_nil,
    dropWithTrace_state,List.length_reverse,BinaryCanonicalMagnitude.trim,BinaryCanonicalMagnitude.bitWork]

theorem reverse_usage (bits : List Bool) : usage (BinarySeedPreparationSpace.reverseWithTrace bits []).2 ≤ 2*bits.length+1 := by
  have hc := reverseWithTrace_cells bits []
  have ha := reverseWithTrace_arrays bits []
  have hf := reverseWithTrace_frames bits []
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

theorem trimWithTrace_usage (bits : List Bool) : usage (trimWithTrace bits).2 ≤ 64*(bits.length+1) := by
  let front := BinarySeedPreparationSpace.reverseWithTrace bits []
  let dropped := dropWithTrace front.1
  let back := BinarySeedPreparationSpace.reverseWithTrace dropped.1.1 []
  have hFront := reverse_usage bits
  have hF : front.1 = bits.reverse := by simp [front,reverseWithTrace_result,List.reverseAux_eq]
  have hDrop : usage dropped.2 ≤ 16*(bits.length+1) := by
    have h := dropWithTrace_usage front.1
    have hLength : front.1.length = bits.length := by rw [hF,List.length_reverse]
    simpa only [hLength] using h
  have hD : dropped.1.1.length ≤ bits.length := by
    dsimp only [dropped]
    rw [dropWithTrace_state,hF]
    simpa only [List.length_reverse] using BinaryBigEndian.trim_length bits.reverse
  have hBack := reverse_usage dropped.1.1
  have hw := wrap_usage 32 (2*bits.length+4) [front.2,dropped.2,back.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage front.2 ≤ _ at hFront
  change usage dropped.2 ≤ _ at hDrop
  change usage back.2 ≤ _ at hBack
  change usage (trimWithTrace bits).2 ≤ _ at hw
  omega

def prepareWithTrace (payload : List Bool) : BinaryStoredDimensionHeader.Header × Trace :=
  let reduced := trimWithTrace payload
  let stored := if reduced.1.1 = [] then [false] else reduced.1.1
  let bytes := stored.map (fun _ => false) ++ true::stored
  let visits := reduced.1.2+4*stored.length+3
  have hBytes : bytes = BinaryNatFrame.encode (BinaryBigEndian.littleValue payload) := by
    change (if reduced.1.1 = [] then [false] else reduced.1.1).map (fun _ => false) ++
      true::(if reduced.1.1 = [] then [false] else reduced.1.1) = _
    dsimp only [reduced]
    rw [trimWithTrace_state]
    exact BinaryStoredNatHeader.header_state payload
  have hVisits : visits ≤ 11*payload.length+12 := by
    change (trimWithTrace payload).1.2+4*(if (trimWithTrace payload).1.1 = [] then [false] else (trimWithTrace payload).1.1).length+3 ≤ _
    rw [trimWithTrace_state]
    exact BinaryStoredNatHeader.visits_bound payload
  (⟨payload,bytes,hBytes,visits,hVisits⟩,
    wrapList (2*stored.length+2) 32 (2*payload.length+stored.length+8) [reduced.2])

theorem prepareWithTrace_state (payload : List Bool) :
    (prepareWithTrace payload).1 = BinaryStoredDimensionHeader.prepare payload := by
  unfold prepareWithTrace BinaryStoredDimensionHeader.prepare BinaryStoredNatHeader.prepare
    BinaryStoredNatHeader.header BinaryStoredNatHeader.visits BinaryStoredNatHeader.payload
  dsimp only
  simp only [trimWithTrace_state]

theorem prepareWithTrace_usage (payload : List Bool) : usage (prepareWithTrace payload).2 ≤ 128*(payload.length+1) := by
  have hTrim := trimWithTrace_usage payload
  let reduced := trimWithTrace payload
  let stored := if reduced.1.1 = [] then [false] else reduced.1.1
  have hStored : stored.length ≤ payload.length+1 := by
    dsimp only [stored,reduced]
    rw [trimWithTrace_state]
    exact BinaryStoredNatHeader.payload_length_le payload
  have hw := wrapList_usage (2*stored.length+2) 32 (2*payload.length+stored.length+8) [reduced.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (prepareWithTrace payload).2 ≤ _ at hw
  change usage reduced.2 ≤ _ at hTrim
  omega

def readWithTrace (frame : List Bool) : Option (BinaryStoredDimensionHeader.Header × List Bool) × Trace :=
  let raw := BinaryUnaryPayloadLifetime.readWithTrace frame
  match raw.1 with
  | none => (none,wrap 16 2 [raw.2])
  | some parsed =>
      let header := prepareWithTrace parsed.1
      (some (header.1,parsed.2),wrap 24 2 [raw.2,header.2])

theorem readWithTrace_state (frame : List Bool) :
    (readWithTrace frame).1 = (BinaryStoredDimensionHeader.read frame).1 := by
  unfold readWithTrace BinaryStoredDimensionHeader.read
  dsimp only
  rw [BinaryUnaryPayloadLifetime.readWithTrace_state]
  cases PositiveBinaryWord.readPayload frame with
  | none => rfl
  | some parsed => simp only [Option.map_some,prepareWithTrace_state]

theorem readWithTrace_usage (frame : List Bool) : usage (readWithTrace frame).2 ≤ 320*(frame.length+1) := by
  have hRaw := BinaryUnaryPayloadLifetime.readWithTrace_usage frame
  unfold readWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(BinaryUnaryPayloadLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryUnaryPayloadLifetime.readWithTrace frame).2]) ≤ _
    omega
  · rename_i parsed hSome
    have hLength := BinaryUnaryPayloadLifetime.read_payload_length frame parsed hSome
    have hHeader := prepareWithTrace_usage parsed.1
    have hw := wrap_usage 24 2 [(BinaryUnaryPayloadLifetime.readWithTrace frame).2,(prepareWithTrace parsed.1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [(BinaryUnaryPayloadLifetime.readWithTrace frame).2,(prepareWithTrace parsed.1).2]) ≤ _
    omega

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (readWithTrace frame).2 steps ≤ borrowed+frame.length+320*(frame.length+1) ∧
    framePeak ((readWithTrace frame).2.take steps) ≤ 320*(frame.length+1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (readWithTrace_usage frame) _ steps

end Blotto.BinaryStoredDimensionHeaderLifetime
