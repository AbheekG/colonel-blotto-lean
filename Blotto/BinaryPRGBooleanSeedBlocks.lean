import Blotto.BinaryPRGTapeSeedBlocks
import Blotto.BinarySeedCursorWork

/-! Actual validation consumes the prepared Boolean rulers. The initial trace
conservatively reserves their retained source regions; its natural sizes are
ghost reservations, not numeric ruler producers. Measured execution uses only
the supplied tapes/rulers and structural cursor/reversal operations. -/
namespace Blotto.BinaryPRGBooleanSeedBlocks
open RationalLottoResourceSystem BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryPRGTapeSeedBlocks
set_option maxHeartbeats 2000000

def readRulersWithTrace (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hChoiceRuler : choiceRuler.length = coinBitBudget n K) (hPrecisionRuler : precisionRuler.length = K) :
    Option (Blocks n K) × Trace :=
  let initialTrace := under 8 (rulerTrace (coinBitBudget n K)) ++ under 8 (rulerTrace K) ++ [.frames 8]
  let choice := consumeWithTrace choiceRuler seed
  let choiceTrace := under 8 choice.2
  match hc : choice.1.1 with
  | none => (none,initialTrace ++ choiceTrace)
  | some first =>
      let scalar := consumeWithTrace precisionRuler first.2
      let scalarTrace := under 8 scalar.2
      match hs : scalar.1.1 with
      | none => (none,initialTrace ++ choiceTrace ++ scalarTrace)
      | some second =>
          let outer := consumeWithTrace precisionRuler second.2
          let outerTrace := under 8 outer.2
          match ho : outer.1.1 with
          | none => (none,initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace)
          | some third =>
              if hEnd : third.2 = [] then
                have hChoice : first.1.length = coinBitBudget n K := by
                  have h := (BinarySeedCursor.consume_success choiceRuler seed first.1 first.2
                    ((consumeWithTrace_option choiceRuler seed).symm.trans hc)).1
                  exact h.trans hChoiceRuler
                have hScalar : second.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler first.2 second.1 second.2
                    ((consumeWithTrace_option precisionRuler first.2).symm.trans hs)).1
                  exact h.trans hPrecisionRuler
                have hOuter : third.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler second.2 third.1 third.2
                    ((consumeWithTrace_option precisionRuler second.2).symm.trans ho)).1
                  exact h.trans hPrecisionRuler
                (some (pack n K first.1 second.1 third.1 hChoice hScalar hOuter),
                  initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace ++ [.arrayAllocation 32])
              else (none,initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace)


def readWithTrace {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    Option (Blocks n prepared.request.precision) × Trace :=
  readRulersWithTrace n prepared.request.precision prepared.choiceRuler prepared.precisionRuler seed
    prepared.choiceRuler_length prepared.precisionRuler_length

theorem read_same {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    readWithTrace prepared seed = BinaryPRGTapeSeedBlocks.readWithTrace n prepared.request.precision seed := by
  cases prepared with
  | mk request header precision choice hp hc =>
    cases hp
    cases hc
    rfl


def readRulersWithWork (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hChoiceRuler : choiceRuler.length = coinBitBudget n K) (hPrecisionRuler : precisionRuler.length = K) :
    Option (Blocks n K) × ℕ :=
  let choice := BinarySeedCursorWork.consumeWithWork choiceRuler seed
  match hc : choice.1 with
  | none => (none,choice.2+4)
  | some first =>
      let scalar := BinarySeedCursorWork.consumeWithWork precisionRuler first.2
      match hs : scalar.1 with
      | none => (none,choice.2+scalar.2+4)
      | some second =>
          let outer := BinarySeedCursorWork.consumeWithWork precisionRuler second.2
          match ho : outer.1 with
          | none => (none,choice.2+scalar.2+outer.2+8)
          | some third =>
              if hEnd : third.2 = [] then
                have hChoice : first.1.length = coinBitBudget n K := by
                  have h := (BinarySeedCursor.consume_success choiceRuler seed first.1 first.2
                    ((BinarySeedCursorWork.consume_state choiceRuler seed).symm.trans hc)).1
                  exact h.trans hChoiceRuler
                have hScalar : second.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler first.2 second.1 second.2
                    ((BinarySeedCursorWork.consume_state precisionRuler first.2).symm.trans hs)).1
                  exact h.trans hPrecisionRuler
                have hOuter : third.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler second.2 third.1 third.2
                    ((BinarySeedCursorWork.consume_state precisionRuler second.2).symm.trans ho)).1
                  exact h.trans hPrecisionRuler
                (some (pack n K first.1 second.1 third.1 hChoice hScalar hOuter),
                  choice.2+scalar.2+outer.2+8)
              else (none,choice.2+scalar.2+outer.2+8)

def raw {n K : ℕ} (blocks : Blocks n K) : List Bool × List Bool × List Bool :=
  (blocks.choice.bits,blocks.scalar.bits,blocks.outer.bits)

theorem raw_injective (n K : ℕ) : Function.Injective (raw (n := n) (K := K)) := by
  intro a b h
  have hc := congrArg Prod.fst h
  have hs := congrArg (fun x : List Bool × List Bool × List Bool => x.2.1) h
  have ho := congrArg (fun x : List Bool × List Bool × List Bool => x.2.2) h
  change a.choice.bits = b.choice.bits at hc
  change a.scalar.bits = b.scalar.bits at hs
  change a.outer.bits = b.outer.bits at ho
  have ec : a.choice = b.choice := by
    apply BinaryScalarTape.ext
    funext j
    simp only [BinaryScalarTape.read,hc]
  have es : a.scalar = b.scalar := by
    apply BinaryScalarTape.ext
    funext j
    simp only [BinaryScalarTape.read,hs]
  have eo : a.outer = b.outer := by
    apply BinaryScalarTape.ext
    funext j
    simp only [BinaryScalarTape.read,ho]
  cases a
  cases b
  dsimp only at ec es eo
  cases ec
  cases es
  cases eo
  rfl

theorem map_raw_injective (n K : ℕ) : Function.Injective (fun x : Option (Blocks n K) => x.map raw) := by
  intro x y h
  cases x with
  | none => cases y <;> simp_all
  | some a => cases y with
    | none => simp only [Option.map_none,Option.map_some] at h; cases h
    | some b => exact congrArg Option.some (raw_injective n K (Option.some.inj h))

-- This raw cursor formula is a ghost specification, not an executed replay.
def readRaw (choiceRuler precisionRuler seed : List Bool) : Option (List Bool × List Bool × List Bool) :=
  match BinarySeedCursor.loop choiceRuler seed [] with
  | none => none
  | some first => match BinarySeedCursor.loop precisionRuler first.2 [] with
    | none => none
    | some second => match BinarySeedCursor.loop precisionRuler second.2 [] with
      | none => none
      | some third => if third.2 = [] then some (first.1,second.1,third.1) else none

theorem readRulers_trace_raw (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hc : choiceRuler.length = coinBitBudget n K) (hp : precisionRuler.length = K) :
    (readRulersWithTrace n K choiceRuler precisionRuler seed hc hp).1.map raw = readRaw choiceRuler precisionRuler seed := by
  unfold readRulersWithTrace
  dsimp only [BinarySeedPreparationSpace.consumeWithTrace]
  split
  · rename_i hC
    have hOld := (cursorWithTrace_result choiceRuler seed []).symm.trans hC
    simp only [readRaw,hOld,Option.map_none]
  · rename_i first hC
    have hOld := (cursorWithTrace_result choiceRuler seed []).symm.trans hC
    simp only [readRaw,hOld]
    split
    · rename_i hS
      have hOldS := (cursorWithTrace_result precisionRuler first.2 []).symm.trans hS
      simp only [hOldS,Option.map_none]
    · rename_i second hS
      have hOldS := (cursorWithTrace_result precisionRuler first.2 []).symm.trans hS
      simp only [hOldS]
      split
      · rename_i hO
        have hOldO := (cursorWithTrace_result precisionRuler second.2 []).symm.trans hO
        simp only [hOldO,Option.map_none]
      · rename_i third hO
        have hOldO := (cursorWithTrace_result precisionRuler second.2 []).symm.trans hO
        simp only [hOldO]
        split <;> simp_all [raw,pack]

theorem readRulers_work_raw (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hc : choiceRuler.length = coinBitBudget n K) (hp : precisionRuler.length = K) :
    (readRulersWithWork n K choiceRuler precisionRuler seed hc hp).1.map raw = readRaw choiceRuler precisionRuler seed := by
  unfold readRulersWithWork
  dsimp only [BinarySeedCursorWork.consumeWithWork]
  split
  · rename_i hC
    have hOld := (BinarySeedCursorWork.loop_state choiceRuler seed []).symm.trans hC
    simp only [readRaw,hOld,Option.map_none]
  · rename_i first hC
    have hOld := (BinarySeedCursorWork.loop_state choiceRuler seed []).symm.trans hC
    simp only [readRaw,hOld]
    split
    · rename_i hS
      have hOldS := (BinarySeedCursorWork.loop_state precisionRuler first.2 []).symm.trans hS
      simp only [hOldS,Option.map_none]
    · rename_i second hS
      have hOldS := (BinarySeedCursorWork.loop_state precisionRuler first.2 []).symm.trans hS
      simp only [hOldS]
      split
      · rename_i hO
        have hOldO := (BinarySeedCursorWork.loop_state precisionRuler second.2 []).symm.trans hO
        simp only [hOldO,Option.map_none]
      · rename_i third hO
        have hOldO := (BinarySeedCursorWork.loop_state precisionRuler second.2 []).symm.trans hO
        simp only [hOldO]
        split <;> simp_all [raw,pack]

theorem readRulers_work_state (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hc : choiceRuler.length = coinBitBudget n K) (hp : precisionRuler.length = K) :
    (readRulersWithWork n K choiceRuler precisionRuler seed hc hp).1 =
      (readRulersWithTrace n K choiceRuler precisionRuler seed hc hp).1 :=
  map_raw_injective n K ((readRulers_work_raw n K choiceRuler precisionRuler seed hc hp).trans
    (readRulers_trace_raw n K choiceRuler precisionRuler seed hc hp).symm)

theorem readRulers_work (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hc : choiceRuler.length = coinBitBudget n K) (hp : precisionRuler.length = K) :
    (readRulersWithWork n K choiceRuler precisionRuler seed hc hp).2 ≤ 8*sampleBitBudget n K+20 := by
  have hN : sampleBitBudget n K = coinBitBudget n K+K+K := by unfold sampleBitBudget innerBitBudget; rfl
  have hC := BinarySeedCursorWork.consume_work choiceRuler seed
  unfold readRulersWithWork
  dsimp only
  split
  · omega
  · rename_i first hFirst
    have hS := BinarySeedCursorWork.consume_work precisionRuler first.2
    split
    · omega
    · rename_i second hSecond
      have hO := BinarySeedCursorWork.consume_work precisionRuler second.2
      split
      · omega
      · split <;> omega

def readWithWork {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    Option (Blocks n prepared.request.precision) × ℕ :=
  readRulersWithWork n prepared.request.precision prepared.choiceRuler prepared.precisionRuler seed
    prepared.choiceRuler_length prepared.precisionRuler_length

theorem read_work_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (readWithWork prepared seed).1 = (readWithTrace prepared seed).1 := readRulers_work_state _ _ _ _ _ _ _

theorem read_work {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (readWithWork prepared seed).2 ≤ 8*sampleBitBudget n prepared.request.precision+20 := readRulers_work _ _ _ _ _ _ _

end Blotto.BinaryPRGBooleanSeedBlocks
