import Blotto.BinaryPRGRequestRulers
import Blotto.BinaryPRGCheckedGameLifetime
import Blotto.BinaryAccuracyLifetime
import Blotto.BinaryPRGAccuracyRulerRequest

/-! Complete raw request reading joins actual game/promise/numerical work
to reached accuracy parsing and one retained ruler precision. Failed games
skip accuracy. Every original typed request/header/suffix/rejection is exact;
all new regions remain retained and raw length derives the full input bound. -/
namespace Blotto.BinaryPRGRawRequestLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000

def readWithTrace (frame : List Bool) : Option ((Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool) × Trace :=
  let game := BinaryPRGCheckedGameLifetime.readWithTrace frame
  match game.1 with
  | none => (none,wrap 16 2 [game.2])
  | some parsed =>
      let accuracy := BinaryAccuracyLifetime.readWithTrace parsed.2
      match accuracy.1 with
      | none => (none,wrap 48 2 [game.2,accuracy.2])
      | some selected =>
          let assembled := BinaryPRGRequestRulers.assembleWithRows parsed.1.2.prepared selected.1
            parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length
          (some (⟨parsed.1.1,assembled.1⟩,selected.2),wrap 64 2 [game.2,accuracy.2,assembled.2])

theorem readWithTrace_state (frame : List Bool) :
    (readWithTrace frame).1 = (BinaryPRGAccuracyRulerRequest.read frame).1 := by
  unfold readWithTrace
  dsimp only
  rw [BinaryPRGCheckedGameLifetime.readWithTrace_state]
  unfold BinaryPRGHeaderFrame.readChecked
  rw [← BinaryPRGStoredDimensionFrame.read_state]
  unfold BinaryPRGAccuracyRulerRequest.read
  dsimp only
  cases hg : (BinaryPRGStoredDimensionFrame.read frame).1 with
  | none => rfl
  | some parsed =>
      dsimp only
      cases hc : (BinaryPRGMeasuredPreparation.prepareChecked parsed.1.2.game.input parsed.1.2.game.canonical).1 with
      | none => rfl
      | some checked =>
          simp only [Option.map_some]
          rw [← BinaryAccuracyLifetime.readWithTrace_state]
          cases ha : (BinaryAccuracyLifetime.readWithTrace parsed.2).1 <;>
            simp only [Option.map_none,Option.map_some,BinaryPRGRequestRulers.assembleWithRows_state]

theorem checked_suffix_length (frame : List Bool) (parsed : (Σ n,BinaryPRGHeaderFrame.Checked n) × List Bool)
    (h : (BinaryPRGCheckedGameLifetime.readWithTrace frame).1 = some parsed) : parsed.2.length ≤ frame.length := by
  rw [BinaryPRGCheckedGameLifetime.readWithTrace_state] at h
  unfold BinaryPRGHeaderFrame.readChecked at h
  cases hg : BinaryPRGHeaderFrame.read frame with
  | none => rw [hg] at h; cases h
  | some game =>
      rw [hg] at h
      obtain ⟨checked,hc,hOut⟩ := Option.map_eq_some_iff.mp h
      subst parsed
      exact BinaryPRGAccuracyRulerRequest.game_suffix_length frame game ((BinaryPRGStoredDimensionFrame.read_state frame).trans hg)

theorem checked_dimension_bound (frame : List Bool) (parsed : (Σ n,BinaryPRGHeaderFrame.Checked n) × List Bool)
    (h : (BinaryPRGCheckedGameLifetime.readWithTrace frame).1 = some parsed) : parsed.1.1 ≤ frame.length := by
  rw [BinaryPRGCheckedGameLifetime.readWithTrace_state] at h
  unfold BinaryPRGHeaderFrame.readChecked at h
  cases hg : BinaryPRGHeaderFrame.read frame with
  | none => rw [hg] at h; cases h
  | some game =>
      rw [hg] at h
      obtain ⟨checked,hc,hOut⟩ := Option.map_eq_some_iff.mp h
      subst parsed
      exact (BinaryDecodedInputLength.parsed_sizes frame game ((BinaryPRGNormalizedFrameWork.read_state frame).trans hg)).1

def envelope (length : ℕ) : ℕ :=
  BinaryPRGCheckedGameLifetime.envelope length+BinaryAccuracyLifetime.envelope length+
    100000*(length+1001)+256

theorem readWithTrace_usage (frame : List Bool) : usage (readWithTrace frame).2 ≤ envelope frame.length := by
  have hGame := BinaryPRGCheckedGameLifetime.readWithTrace_usage frame
  unfold readWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(BinaryPRGCheckedGameLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryPRGCheckedGameLifetime.readWithTrace frame).2]) ≤ _
    unfold envelope
    omega
  · rename_i parsed hSome
    have hLength := checked_suffix_length frame parsed hSome
    have hn := checked_dimension_bound frame parsed hSome
    have hAccuracy := (BinaryAccuracyLifetime.readWithTrace_usage parsed.2).trans (BinaryAccuracyLifetime.envelope_mono hLength)
    split
    · have hw := wrap_usage 48 2 [(BinaryPRGCheckedGameLifetime.readWithTrace frame).2,(BinaryAccuracyLifetime.readWithTrace parsed.2).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 48 2 [(BinaryPRGCheckedGameLifetime.readWithTrace frame).2,(BinaryAccuracyLifetime.readWithTrace parsed.2).2]) ≤ _
      unfold envelope
      omega
    · rename_i selected hSelected
      have hWidth := BinaryAccuracyRulerReadWork.read_widths parsed.2 selected
        ((BinaryAccuracyLifetime.readWithTrace_state parsed.2).symm.trans hSelected)
      have hAssembly := BinaryPRGRequestRulers.assembleWithRows_usage parsed.1.2.prepared selected.1
        parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length
      have hw := wrap_usage 64 2 [(BinaryPRGCheckedGameLifetime.readWithTrace frame).2,
        (BinaryAccuracyLifetime.readWithTrace parsed.2).2,
        (BinaryPRGRequestRulers.assembleWithRows parsed.1.2.prepared selected.1 parsed.1.2.header
          parsed.1.2.rows parsed.1.2.rows_length).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 64 2 [(BinaryPRGCheckedGameLifetime.readWithTrace frame).2,
        (BinaryAccuracyLifetime.readWithTrace parsed.2).2,
        (BinaryPRGRequestRulers.assembleWithRows parsed.1.2.prepared selected.1 parsed.1.2.header
          parsed.1.2.rows parsed.1.2.rows_length).2]) ≤ _
      unfold envelope
      omega

theorem envelope_polynomial (length : ℕ) : envelope length ≤ 500000000000000*(length+8)^8 := by
  have hInput := BinaryPRGCheckedGameLifetime.envelope_polynomial length
  have hPower := Nat.pow_le_pow_left (show length+4 ≤ length+8 by omega) 8
  have hLinear : length+8 ≤ (length+8)^8 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < length+8) (show 1 ≤ 8 by omega)
  have hOne := Nat.one_le_pow 8 (length+8) (by omega)
  unfold envelope BinaryAccuracyLifetime.envelope
  nlinarith only [hInput,hPower,hLinear,hOne]

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (readWithTrace frame).2 steps ≤ borrowed+frame.length+envelope frame.length ∧
    framePeak ((readWithTrace frame).2.take steps) ≤ envelope frame.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (readWithTrace_usage frame) _ steps

end Blotto.BinaryPRGRawRequestLifetime
