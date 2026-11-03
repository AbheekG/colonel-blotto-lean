import Blotto.BinaryReferenceVectorLifetime
import Blotto.BinaryPRGOutputLifetime

/-! Coordinate framing follows actual Boolean rulers. Numeric lengths occur
only in erased bounds/work annotations, never as data-loop counters. -/
namespace Blotto.BinaryTapeFrameLifetime
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def rulerWithWork : List Bool → List Bool × ℕ
  | [] => ([],2)
  | _::rest => let later := rulerWithWork rest; (false::later.1,later.2+4)

def rulerWithTrace : List Bool → List Bool × Trace
  | [] => ([],wrap 8 1 [])
  | _::rest => let later := rulerWithTrace rest; (false::later.1,wrap 16 1 [later.2])

theorem ruler_work_state (bits : List Bool) : (rulerWithWork bits).1 = List.replicate bits.length false := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [rulerWithWork,List.length_cons,List.replicate_succ,ih]

theorem ruler_state (bits : List Bool) : (rulerWithTrace bits).1 = (rulerWithWork bits).1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [rulerWithTrace,rulerWithWork,ih]

theorem ruler_work (bits : List Bool) : (rulerWithWork bits).2 = 4*bits.length+2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [rulerWithWork,List.length_cons,ih]; omega

theorem ruler_usage (bits : List Bool) : usage (rulerWithTrace bits).2 ≤ 20*bits.length+16 := by
  induction bits with
  | nil => exact (wrap_usage 8 1 []).trans (by simp)
  | cons bit rest ih =>
      have hw := wrap_usage 16 1 [(rulerWithTrace rest).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (rulerWithTrace (bit::rest)).2 ≤ _ at hw
      simp only [List.length_cons]
      omega

def payloadWithWork (bits : List Bool) : List Bool × ℕ :=
  let ruler := rulerWithWork bits
  let joined := BinaryPRGWordStoreHeapMachine.appendWithWork ruler.1 (true::bits)
  (joined.1,ruler.2+joined.2.work+4)

def payloadWithTrace (bits : List Bool) : List Bool × Trace :=
  let ruler := rulerWithTrace bits
  let joined := BinaryPRGHeapPrimitiveLifetime.appendWithTrace ruler.1 (true::bits)
  (joined.1,wrap 32 2 [ruler.2,joined.2])

theorem payload_work_state (bits : List Bool) : (payloadWithWork bits).1 = BinaryStoredRowFrame.payload bits := by
  simp only [payloadWithWork,BinaryPRGWordStoreHeapMachine.appendWithWork_erasure,ruler_work_state,BinaryStoredRowFrame.payload]

theorem payload_state (bits : List Bool) : (payloadWithTrace bits).1 = (payloadWithWork bits).1 := by
  simp only [payloadWithTrace,payloadWithWork,BinaryPRGHeapPrimitiveLifetime.appendWithTrace_erasure,ruler_state]

theorem payload_work (bits : List Bool) : (payloadWithWork bits).2 ≤ 16*(bits.length+1) := by
  have hp := BinaryPRGWordStoreHeapMachine.appendWithWork_price (rulerWithWork bits).1 (true::bits)
  have hLength : (rulerWithWork bits).1.length = bits.length := by rw [ruler_work_state,List.length_replicate]
  rw [hLength] at hp
  simp only [payloadWithWork,ruler_work]
  omega

theorem payload_usage (bits : List Bool) : usage (payloadWithTrace bits).2 ≤ 256*(bits.length+1) := by
  have hr := ruler_usage bits
  have ha := BinaryReferenceVectorLifetime.append_usage (rulerWithTrace bits).1 (true::bits)
  have hLength : (rulerWithTrace bits).1.length = bits.length := by rw [ruler_state,ruler_work_state,List.length_replicate]
  rw [hLength] at ha
  have hw := wrap_usage 32 2 [(rulerWithTrace bits).2,
    (BinaryPRGHeapPrimitiveLifetime.appendWithTrace (rulerWithTrace bits).1 (true::bits)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (payloadWithTrace bits).2 ≤ _ at hw
  omega

def wordWithWork (word : SignedWord) : List Bool × ℕ :=
  let numerator := payloadWithWork word.numerator
  let denominator := payloadWithWork word.denominator
  let joined := BinaryPRGWordStoreHeapMachine.appendWithWork numerator.1 denominator.1
  (word.negative::joined.1,numerator.2+denominator.2+joined.2.work+8)

def wordWithTrace (word : SignedWord) : List Bool × Trace :=
  let numerator := payloadWithTrace word.numerator
  let denominator := payloadWithTrace word.denominator
  let joined := BinaryPRGHeapPrimitiveLifetime.appendWithTrace numerator.1 denominator.1
  (word.negative::joined.1,wrap 48 2 [numerator.2,denominator.2,joined.2])

theorem word_work_state (word : SignedWord) : (wordWithWork word).1 = BinaryStoredRowFrame.word word := by
  simp only [wordWithWork,payload_work_state,BinaryPRGWordStoreHeapMachine.appendWithWork_erasure,BinaryStoredRowFrame.word]

theorem word_state (word : SignedWord) : (wordWithTrace word).1 = (wordWithWork word).1 := by
  simp only [wordWithTrace,wordWithWork,payload_state,BinaryPRGHeapPrimitiveLifetime.appendWithTrace_erasure]

theorem word_work (word : SignedWord) : (wordWithWork word).2 ≤ 128*(width word+1) := by
  have hn := payload_work word.numerator
  have hd := payload_work word.denominator
  have ha := BinaryPRGWordStoreHeapMachine.appendWithWork_price (payloadWithWork word.numerator).1 (payloadWithWork word.denominator).1
  have hLength : (payloadWithWork word.numerator).1.length = 2*word.numerator.length+1 := by rw [payload_work_state,BinaryPRGOutputLifetime.payload_length]
  rw [hLength] at ha
  have hN : word.numerator.length ≤ width word := Nat.le_max_left _ _
  have hD : word.denominator.length ≤ width word := Nat.le_max_right _ _
  change _+_+_+8 ≤ _
  omega

theorem word_usage (word : SignedWord) : usage (wordWithTrace word).2 ≤ 1024*(width word+1) := by
  have hn := payload_usage word.numerator
  have hd := payload_usage word.denominator
  have ha := BinaryReferenceVectorLifetime.append_usage (payloadWithTrace word.numerator).1 (payloadWithTrace word.denominator).1
  have hLength : (payloadWithTrace word.numerator).1.length = 2*word.numerator.length+1 := by rw [payload_state,payload_work_state,BinaryPRGOutputLifetime.payload_length]
  rw [hLength] at ha
  have hN : word.numerator.length ≤ width word := Nat.le_max_left _ _
  have hD : word.denominator.length ≤ width word := Nat.le_max_right _ _
  have hw := wrap_usage 48 2 [(payloadWithTrace word.numerator).2,(payloadWithTrace word.denominator).2,
    (BinaryPRGHeapPrimitiveLifetime.appendWithTrace (payloadWithTrace word.numerator).1 (payloadWithTrace word.denominator).1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wordWithTrace word).2 ≤ _ at hw
  omega

theorem word_length (word : SignedWord) : (wordWithTrace word).1.length ≤ 4*width word+3 := by
  rw [word_state,word_work_state,BinaryPRGOutputLifetime.word_length]
  have hN : word.numerator.length ≤ width word := Nat.le_max_left _ _
  have hD : word.denominator.length ≤ width word := Nat.le_max_right _ _
  omega

end Blotto.BinaryTapeFrameLifetime
