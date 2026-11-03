import Blotto.BinaryDecodedInputLength
import Blotto.UnaryPayloadWork

/-! A dimension header retains the original Boolean payload and produces its
canonical bytes once. No numeric declared dimension is assembled by this
reader. Its numeric interpretation is only a refinement specification. -/

namespace Blotto.BinaryStoredDimensionHeader

structure Header where
  payload : List Bool
  bytes : List Bool
  correct : bytes = BinaryNatFrame.encode (BinaryBigEndian.littleValue payload)
  visits : ℕ
  visits_bound : visits ≤ 11 * payload.length + 12

def prepare (payload : List Bool) : Header :=
  let stored := BinaryStoredNatHeader.prepare payload
  ⟨payload,stored.1,BinaryStoredNatHeader.prepare_state payload,stored.2,BinaryStoredNatHeader.prepare_bound payload⟩

def Header.typed (header : Header) : BinaryPRGHeaderFrame.Header (BinaryBigEndian.littleValue header.payload) :=
  ⟨header.bytes,header.correct,header.visits,header.payload.length,header.visits_bound⟩

def interpret (parsed : Header × List Bool) : (Σ n, BinaryPRGHeaderFrame.Header n) × List Bool :=
  (⟨BinaryBigEndian.littleValue parsed.1.payload,parsed.1.typed⟩,parsed.2)

def read (frame : List Bool) : Option (Header × List Bool) × ℕ :=
  let parsed := (PositiveBinaryWord.readPayload frame).map (fun raw => (prepare raw.1,raw.2))
  let visits := UnaryPayload.readSteps frame + match parsed with
    | none => 0
    | some result => result.1.visits
  (parsed,visits)

theorem typed_heq {n m : ℕ} (first : BinaryPRGHeaderFrame.Header n) (second : BinaryPRGHeaderFrame.Header m)
    (hn : n = m) (hb : first.bytes = second.bytes) (hv : first.visits = second.visits) (hw : first.sourceWidth = second.sourceWidth) :
    HEq first second := by
  subst m
  cases first
  cases second
  dsimp only at hb hv hw
  cases hb
  cases hv
  cases hw
  rfl

theorem read_state (frame : List Bool) : (read frame).1.map interpret = BinaryPRGHeaderFrame.readHeader frame := by
  unfold read BinaryPRGHeaderFrame.readHeader
  dsimp only
  cases hr : PositiveBinaryWord.readPayload frame with
  | none => rfl
  | some raw =>
      simp only [Option.map_some,interpret,prepare,Header.typed]
      apply congrArg some
      apply Prod.ext
      · apply Sigma.ext (BinaryBigEndian.littleValue_decode raw.1)
        exact typed_heq _ _ (BinaryBigEndian.littleValue_decode raw.1) rfl rfl rfl
      · rfl

theorem read_payload_length (frame : List Bool) (parsed : Header × List Bool)
    (h : (read frame).1 = some parsed) : parsed.1.payload.length ≤ frame.length := by
  unfold read at h
  obtain ⟨raw,hr,hOut⟩ := Option.map_eq_some_iff.mp h
  subst parsed
  exact BinaryPRGHeaderFrame.readPayload_length_bound frame raw.1 raw.2 hr

theorem read_suffix_length (frame : List Bool) (parsed : Header × List Bool)
    (h : (read frame).1 = some parsed) : parsed.2.length ≤ frame.length := by
  have hs := read_state frame
  rw [h,Option.map_some] at hs
  exact BinaryPRGNormalizedFrameWork.header_suffix_length frame (interpret parsed) hs.symm

theorem read_bound (frame : List Bool) : (read frame).2 ≤ 12 * frame.length + 13 := by
  have hu := UnaryPayload.readSteps_bound frame
  unfold read
  dsimp only
  cases hr : (PositiveBinaryWord.readPayload frame).map (fun raw => (prepare raw.1,raw.2)) with
  | none => dsimp only; omega
  | some parsed =>
      have hs := Header.visits_bound parsed.1
      have hp := read_payload_length frame parsed hr
      dsimp only
      omega

end Blotto.BinaryStoredDimensionHeader
