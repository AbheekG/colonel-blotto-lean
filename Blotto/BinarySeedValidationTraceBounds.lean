import Blotto.BinaryTerminalPhysicalCompleteSeedBounds
import Blotto.BinaryResourceTraceLength

/-! Structural seed validation event counts are bounded by reached source work.
No scan of an arbitrarily long supplied seed is assumed or charged implicitly. -/
namespace Blotto.BinarySeedValidationTraceBounds
open BinarySeedPreparationSpace RationalLottoResourceSystem
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem cursor_length_work (ruler bits reversed : List Bool) (depth : ℕ) :
    (BinarySeedCursorMeasured.loopAt ruler bits reversed depth).trace.length ≤
      (BinarySeedCursorMeasured.loopAt ruler bits reversed depth).work := by
  induction ruler generalizing bits reversed depth with
  | nil =>
      simp only [BinarySeedCursorMeasured.loopAt,List.length_cons,BinarySeedCursorMeasured.reverseAt_trace_length,
        BinarySeedCursorMeasured.reverseAt_work,BinaryMidpointTapeLifetime.reverse_work]
      omega
  | cons marker ruler ih => cases bits with
    | nil => simp [BinarySeedCursorMeasured.loopAt]
    | cons bit bits =>
        have h := ih bits (bit::reversed) (depth+1)
        simp only [BinarySeedCursorMeasured.loopAt,List.length_cons]
        omega

theorem consume_length_work (ruler bits : List Bool) :
    (BinarySeedCursorMeasured.consume ruler bits).1.2.length ≤
      (BinarySeedCursorMeasured.consume ruler bits).2+1 := by
  have h := cursor_length_work ruler bits [] 0
  simpa only [BinarySeedCursorMeasured.consume,BinarySeedCursorMeasured.loop,List.length_append,
    List.length_cons,List.length_nil] using Nat.add_le_add_right h 1

theorem read_rulers_length (n K : ℕ) (choice precision seed : List Bool)
    (hc : choice.length = coinBitBudget n K) (hp : precision.length = K) :
    (BinarySeedPreparationMeasured.readRulers n K choice precision seed hc hp).1.2.length ≤
      (BinarySeedPreparationMeasured.readRulers n K choice precision seed hc hp).2+5 := by
  have hC := consume_length_work choice seed
  unfold BinarySeedPreparationMeasured.readRulers
  dsimp only
  split
  · simp only [List.length_append,under_length,rulerTrace,List.length_cons,List.length_nil]
    omega
  · rename_i first hFirst
    have hS := consume_length_work precision first.2
    split
    · simp only [List.length_append,under_length,rulerTrace,List.length_cons,List.length_nil]
      omega
    · rename_i second hSecond
      have hO := consume_length_work precision second.2
      split
      · simp only [List.length_append,under_length,rulerTrace,List.length_cons,List.length_nil]
        omega
      · split <;> simp only [List.length_append,under_length,rulerTrace,List.length_cons,List.length_nil] <;> omega

theorem preparation_length {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (BinarySeedPreparationMeasured.prepare request seed).1.2.length ≤
      (BinarySeedPreparationMeasured.prepare request seed).2+5 := by
  have h := read_rulers_length n request.request.precision request.choiceRuler request.precisionRuler seed
    request.choiceRuler_length request.precisionRuler_length
  change (BinarySeedPreparationMeasured.read request seed).1.2.length ≤ (BinarySeedPreparationMeasured.read request seed).2+5 at h
  unfold BinarySeedPreparationMeasured.prepare
  dsimp only
  split <;> dsimp only <;> omega

theorem store_length_work (seed : List Bool) : (BinaryWordStoreLifetime.prepareWithTrace seed).2.length ≤
    2*(BinaryWordStoreMeasured.prepare seed).2 := by
  have h := BinaryWordStoreMeasured.preparePlan_budget seed
  rw [← BinaryWordStoreMeasured.prepare_erases]
  simp only [BinaryWordStoreMeasured.prepare,BinaryWordStoreMeasured.prepareMeasured,
    BinaryTracePlanMeasured.emit_length,List.length_nil,Nat.add_zero]
  omega

theorem store_length (frame : List Bool) (parsed : BinaryTerminalPhysicalAllowanceCache.Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1 parsed.1.2.logical.request.precision) :
    (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).2.length ≤ 1000000*(frame.length+1) := by
  have h := store_length_work blocks.choice.bits
  have hw := BinaryWordStoreMeasured.prepare_bound blocks.choice.bits
  have hs := BinaryTerminalPhysicalAllowanceSeed.accepted_store_size frame parsed hParsed blocks
  have hv : (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1.cap.value = blocks.choice.bits.length := by
    rw [BinaryWordStoreLifetime.prepareWithTrace_erases,BinarySeedLookupTree.prepare_cap]
  dsimp only at hs
  rw [hv] at hs
  omega

end Blotto.BinarySeedValidationTraceBounds
