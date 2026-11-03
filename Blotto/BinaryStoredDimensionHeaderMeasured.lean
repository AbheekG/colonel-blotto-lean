import Blotto.BinaryUnaryPayloadMeasured
import Blotto.BinaryStoredDimensionControlMeasured

/-! The dimension header is built by actual reverse/drop/reverse, false-map
and append loops. The data and conservative old region trace are unchanged.
Old visit/length/reservation fields and the added work field are ghost
observers: native arithmetic for those fields is outside this source price. -/
namespace Blotto.BinaryStoredDimensionHeaderMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def falseMap : List Bool → List Bool × ℕ
  | [] => ([],2)
  | _::rest => let later := falseMap rest; (false::later.1,later.2+4)

theorem falseMap_data (bits : List Bool) : (falseMap bits).1 = bits.map (fun _ => false) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [falseMap,List.map_cons,ih]

theorem falseMap_work (bits : List Bool) : (falseMap bits).2 = 4*bits.length+2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [falseMap,List.length_cons,ih]; omega

def append : List Bool → List Bool → List Bool × ℕ
  | [],right => (right,2)
  | bit::left,right => let later := append left right; (bit::later.1,later.2+4)

theorem append_data (left right : List Bool) : (append left right).1 = left++right := by
  induction left with
  | nil => rfl
  | cons bit left ih => simp only [append,List.cons_append,ih]

theorem append_work (left right : List Bool) : (append left right).2 = 4*left.length+2 := by
  induction left with
  | nil => rfl
  | cons bit left ih => simp only [append,List.length_cons,ih]; omega

def trim (bits : List Bool) : ((List Bool × ℕ) × Trace) × ℕ :=
  let front := BinarySeedCursorMeasured.reverse bits []
  let dropped := BinaryStoredDimensionControlMeasured.drop front.1.1
  let back := BinarySeedCursorMeasured.reverse dropped.1.1.1 []
  let visits := 2*bits.length+3*dropped.1.1.2+2*back.1.1.length+2
  (((back.1.1,visits),wrap 32 (2*bits.length+4) [front.1.2,dropped.1.2,back.1.2]),
    front.2+dropped.2+back.2+8)

theorem trim_erases (bits : List Bool) :
    (trim bits).1 = BinaryStoredDimensionHeaderLifetime.trimWithTrace bits := by
  simp only [trim,BinaryStoredDimensionHeaderLifetime.trimWithTrace,
    BinarySeedCursorMeasured.reverse_erases,BinaryStoredDimensionControlMeasured.drop_erases]

theorem trim_work (bits : List Bool) : (trim bits).2 ≤ 32*(bits.length+1) := by
  let front := BinarySeedCursorMeasured.reverse bits []
  let dropped := BinaryStoredDimensionControlMeasured.drop front.1.1
  have hf := BinarySeedCursorMeasured.reverse_work bits []
  rw [BinaryMidpointTapeLifetime.reverse_work] at hf
  have hLength : front.1.1.length = bits.length := by
    simp only [front,BinarySeedCursorMeasured.reverse_erases,reverseWithTrace_result,
      List.reverseAux_eq,List.append_nil,List.length_reverse]
  have hd := BinaryStoredDimensionControlMeasured.drop_work front.1.1
  have hDLength := BinaryStoredDimensionControlMeasured.drop_length front.1.1
  have hb := BinarySeedCursorMeasured.reverse_work dropped.1.1.1 []
  rw [BinaryMidpointTapeLifetime.reverse_work] at hb
  change front.2 = _ at hf
  change dropped.2 ≤ _ at hd
  change dropped.1.1.1.length ≤ _ at hDLength
  change front.2+dropped.2+(BinarySeedCursorMeasured.reverse dropped.1.1.1 []).2+8 ≤ _
  omega

def prepare (payload : List Bool) : (BinaryStoredDimensionHeader.Header × Trace) × ℕ :=
  let reduced := trim payload
  let stored := if reduced.1.1.1 = [] then [false] else reduced.1.1.1
  let zeros := falseMap stored
  let joined := append zeros.1 (true::stored)
  let bytes := joined.1
  let visits := reduced.1.1.2+4*stored.length+3
  have hData : bytes = stored.map (fun _ => false) ++ true::stored := by
    dsimp only [bytes,joined]
    rw [append_data,falseMap_data]
  have hBytes : bytes = BinaryNatFrame.encode (BinaryBigEndian.littleValue payload) := by
    rw [hData]
    dsimp only [stored,reduced]
    rw [trim_erases,BinaryStoredDimensionHeaderLifetime.trimWithTrace_state]
    exact BinaryStoredNatHeader.header_state payload
  have hVisits : visits ≤ 11*payload.length+12 := by
    dsimp only [visits,stored,reduced]
    rw [trim_erases,BinaryStoredDimensionHeaderLifetime.trimWithTrace_state]
    exact BinaryStoredNatHeader.visits_bound payload
  ((⟨payload,bytes,hBytes,visits,hVisits⟩,
    wrapList (2*stored.length+2) 32 (2*payload.length+stored.length+8) [reduced.1.2]),
    reduced.2+zeros.2+joined.2+8)

theorem prepare_erases (payload : List Bool) :
    (prepare payload).1 = BinaryStoredDimensionHeaderLifetime.prepareWithTrace payload := by
  simp only [prepare,BinaryStoredDimensionHeaderLifetime.prepareWithTrace,trim_erases,
    append_data,falseMap_data]

theorem prepare_work (payload : List Bool) : (prepare payload).2 ≤ 64*(payload.length+1) := by
  have ht := trim_work payload
  let stored := if (trim payload).1.1.1 = [] then [false] else (trim payload).1.1.1
  have hStored : stored.length ≤ payload.length+1 := by
    dsimp only [stored]
    rw [trim_erases,BinaryStoredDimensionHeaderLifetime.trimWithTrace_state]
    exact BinaryStoredNatHeader.payload_length_le payload
  have hZeros := falseMap_work stored
  have hJoined := append_work (falseMap stored).1 (true::stored)
  have hZeroLength : (falseMap stored).1.length = stored.length := by rw [falseMap_data,List.length_map]
  change (trim payload).2+(falseMap stored).2+(append (falseMap stored).1 (true::stored)).2+8 ≤ _
  omega

def read (frame : List Bool) : (Option (BinaryStoredDimensionHeader.Header × List Bool) × Trace) × ℕ :=
  let raw := BinaryUnaryPayloadMeasured.read frame
  match raw.1.1 with
  | none => ((none,wrap 16 2 [raw.1.2]),raw.2+4)
  | some parsed =>
      let header := prepare parsed.1
      ((some (header.1.1,parsed.2),wrap 24 2 [raw.1.2,header.1.2]),raw.2+header.2+8)

theorem read_erases (frame : List Bool) :
    (read frame).1 = BinaryStoredDimensionHeaderLifetime.readWithTrace frame := by
  unfold read BinaryStoredDimensionHeaderLifetime.readWithTrace
  dsimp only
  simp only [BinaryUnaryPayloadMeasured.read_erases,prepare_erases]
  cases (BinaryUnaryPayloadLifetime.readWithTrace frame).1 <;> rfl

theorem read_work (frame : List Bool) : (read frame).2 ≤ 128*(frame.length+1) := by
  have hr := BinaryUnaryPayloadMeasured.read_work frame
  unfold read
  dsimp only
  split
  · omega
  · rename_i parsed hSome
    have hl := BinaryUnaryPayloadMeasured.read_payload_length frame parsed hSome
    have hp := prepare_work parsed.1
    omega

theorem read_usage (frame : List Bool) : usage (read frame).1.2 ≤ 320*(frame.length+1) := by
  rw [read_erases]
  exact BinaryStoredDimensionHeaderLifetime.readWithTrace_usage frame

theorem read_payload_length (frame : List Bool) (parsed : BinaryStoredDimensionHeader.Header × List Bool)
    (h : (read frame).1.1 = some parsed) : parsed.1.payload.length ≤ frame.length :=
  BinaryStoredDimensionHeader.read_payload_length frame parsed
    ((BinaryStoredDimensionHeaderLifetime.readWithTrace_state frame).symm.trans
      ((congrArg Prod.fst (read_erases frame)).symm.trans h))

theorem read_suffix_length (frame : List Bool) (parsed : BinaryStoredDimensionHeader.Header × List Bool)
    (h : (read frame).1.1 = some parsed) : parsed.2.length ≤ frame.length :=
  BinaryStoredDimensionHeader.read_suffix_length frame parsed
    ((BinaryStoredDimensionHeaderLifetime.readWithTrace_state frame).symm.trans
      ((congrArg Prod.fst (read_erases frame)).symm.trans h))

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (read frame).1.2 steps ≤ borrowed+frame.length+320*(frame.length+1) ∧
    framePeak ((read frame).1.2.take steps) ≤ 320*(frame.length+1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (read_usage frame) _ steps

end Blotto.BinaryStoredDimensionHeaderMeasured
