import Blotto.BinarySeedCursorMeasured
import Blotto.BinaryWordStoreMeasured
import Blotto.BinaryPRGSeedPreparationWork

/-! Validation and physical choice-store construction return their data,
allocation traces and source work from the same execution. Length witnesses
are erased proofs; no native seed-length/countdown is used for validation. -/

namespace Blotto.BinarySeedPreparationMeasured
open RationalLottoResourceSystem BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGTapeSeedBlocks
set_option autoImplicit false
set_option maxHeartbeats 2500000

def readRulers (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hChoiceRuler : choiceRuler.length = coinBitBudget n K)
    (hPrecisionRuler : precisionRuler.length = K) : (Option (Blocks n K) × Trace) × ℕ :=
  let initialTrace := under 8 (rulerTrace (coinBitBudget n K))++
    under 8 (rulerTrace K)++[.frames 8]
  let choice := BinarySeedCursorMeasured.consume choiceRuler seed
  let choiceTrace := under 8 choice.1.2
  match hc : choice.1.1 with
  | none => ((none,initialTrace++choiceTrace),choice.2+4)
  | some first =>
      let scalar := BinarySeedCursorMeasured.consume precisionRuler first.2
      let scalarTrace := under 8 scalar.1.2
      match hs : scalar.1.1 with
      | none => ((none,initialTrace++choiceTrace++scalarTrace),choice.2+scalar.2+4)
      | some second =>
          let outer := BinarySeedCursorMeasured.consume precisionRuler second.2
          let outerTrace := under 8 outer.1.2
          match ho : outer.1.1 with
          | none => ((none,initialTrace++choiceTrace++scalarTrace++outerTrace),
              choice.2+scalar.2+outer.2+8)
          | some third =>
              if hEnd : third.2 = [] then
                have hChoice : first.1.length = coinBitBudget n K := by
                  have h := (BinarySeedCursor.consume_success choiceRuler seed first.1 first.2
                    ((consumeWithTrace_option choiceRuler seed).symm.trans
                      ((BinarySeedCursorMeasured.consume_data choiceRuler seed).symm.trans hc))).1
                  exact h.trans hChoiceRuler
                have hScalar : second.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler first.2 second.1 second.2
                    ((consumeWithTrace_option precisionRuler first.2).symm.trans
                      ((BinarySeedCursorMeasured.consume_data precisionRuler first.2).symm.trans hs))).1
                  exact h.trans hPrecisionRuler
                have hOuter : third.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler second.2 third.1 third.2
                    ((consumeWithTrace_option precisionRuler second.2).symm.trans
                      ((BinarySeedCursorMeasured.consume_data precisionRuler second.2).symm.trans ho))).1
                  exact h.trans hPrecisionRuler
                ((some (pack n K first.1 second.1 third.1 hChoice hScalar hOuter),
                  initialTrace++choiceTrace++scalarTrace++outerTrace++[.arrayAllocation 32]),
                  choice.2+scalar.2+outer.2+8)
              else ((none,initialTrace++choiceTrace++scalarTrace++outerTrace),
                choice.2+scalar.2+outer.2+8)

theorem readRulers_raw (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hc : choiceRuler.length = coinBitBudget n K) (hp : precisionRuler.length = K) :
    (readRulers n K choiceRuler precisionRuler seed hc hp).1.1.map
        BinaryPRGBooleanSeedBlocks.raw =
      BinaryPRGBooleanSeedBlocks.readRaw choiceRuler precisionRuler seed := by
  unfold readRulers
  dsimp only
  split
  · rename_i hC
    have hOld := (consumeWithTrace_option choiceRuler seed).symm.trans
      ((BinarySeedCursorMeasured.consume_data choiceRuler seed).symm.trans hC)
    change BinarySeedCursor.loop choiceRuler seed [] = none at hOld
    simp only [BinaryPRGBooleanSeedBlocks.readRaw,hOld,Option.map_none]
  · rename_i first hC
    have hOld := (consumeWithTrace_option choiceRuler seed).symm.trans
      ((BinarySeedCursorMeasured.consume_data choiceRuler seed).symm.trans hC)
    change BinarySeedCursor.loop choiceRuler seed [] = some first at hOld
    simp only [BinaryPRGBooleanSeedBlocks.readRaw,hOld]
    split
    · rename_i hS
      have hOldS := (consumeWithTrace_option precisionRuler first.2).symm.trans
        ((BinarySeedCursorMeasured.consume_data precisionRuler first.2).symm.trans hS)
      change BinarySeedCursor.loop precisionRuler first.2 [] = none at hOldS
      simp only [hOldS,Option.map_none]
    · rename_i second hS
      have hOldS := (consumeWithTrace_option precisionRuler first.2).symm.trans
        ((BinarySeedCursorMeasured.consume_data precisionRuler first.2).symm.trans hS)
      change BinarySeedCursor.loop precisionRuler first.2 [] = some second at hOldS
      simp only [hOldS]
      split
      · rename_i hO
        have hOldO := (consumeWithTrace_option precisionRuler second.2).symm.trans
          ((BinarySeedCursorMeasured.consume_data precisionRuler second.2).symm.trans hO)
        change BinarySeedCursor.loop precisionRuler second.2 [] = none at hOldO
        simp only [hOldO,Option.map_none]
      · rename_i third hO
        have hOldO := (consumeWithTrace_option precisionRuler second.2).symm.trans
          ((BinarySeedCursorMeasured.consume_data precisionRuler second.2).symm.trans hO)
        change BinarySeedCursor.loop precisionRuler second.2 [] = some third at hOldO
        simp only [hOldO]
        split <;> simp_all only [BinaryPRGBooleanSeedBlocks.raw,pack,
          Option.map_some,Option.map_none,ite_true,ite_false]

theorem readRulers_data (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hc : choiceRuler.length = coinBitBudget n K) (hp : precisionRuler.length = K) :
    (readRulers n K choiceRuler precisionRuler seed hc hp).1.1 =
      (BinaryPRGBooleanSeedBlocks.readRulersWithTrace n K choiceRuler precisionRuler seed hc hp).1 :=
  BinaryPRGBooleanSeedBlocks.map_raw_injective n K
    ((readRulers_raw n K choiceRuler precisionRuler seed hc hp).trans
      (BinaryPRGBooleanSeedBlocks.readRulers_trace_raw n K choiceRuler precisionRuler seed hc hp).symm)

def referenceTrace (n K : ℕ) (choiceRuler precisionRuler seed : List Bool) : Trace :=
  let initialTrace := under 8 (rulerTrace (coinBitBudget n K))++under 8 (rulerTrace K)++[.frames 8]
  let choice := consumeWithTrace choiceRuler seed
  match choice.1.1 with
  | none => initialTrace++under 8 choice.2
  | some first =>
      let scalar := consumeWithTrace precisionRuler first.2
      match scalar.1.1 with
      | none => initialTrace++under 8 choice.2++under 8 scalar.2
      | some second =>
          let outer := consumeWithTrace precisionRuler second.2
          match outer.1.1 with
          | none => initialTrace++under 8 choice.2++under 8 scalar.2++under 8 outer.2
          | some third =>
              if third.2 = [] then
                initialTrace++under 8 choice.2++under 8 scalar.2++under 8 outer.2++[.arrayAllocation 32]
              else initialTrace++under 8 choice.2++under 8 scalar.2++under 8 outer.2

theorem reference_trace (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hc : choiceRuler.length = coinBitBudget n K) (hp : precisionRuler.length = K) :
    (BinaryPRGBooleanSeedBlocks.readRulersWithTrace n K choiceRuler precisionRuler seed hc hp).2 =
      referenceTrace n K choiceRuler precisionRuler seed := by
  unfold BinaryPRGBooleanSeedBlocks.readRulersWithTrace
  dsimp only
  split
  · rename_i hC
    simp only [referenceTrace,hC]
  · rename_i first hC
    simp only [referenceTrace,hC]
    split
    · rename_i hS
      simp only [hS]
    · rename_i second hS
      simp only [hS]
      split
      · rename_i hO
        simp only [hO]
      · rename_i third hO
        simp only [hO]
        split <;> simp_all only [ite_true,ite_false]

theorem readRulers_trace (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hc : choiceRuler.length = coinBitBudget n K) (hp : precisionRuler.length = K) :
    (readRulers n K choiceRuler precisionRuler seed hc hp).1.2 =
      (BinaryPRGBooleanSeedBlocks.readRulersWithTrace n K choiceRuler precisionRuler seed hc hp).2 := by
  rw [reference_trace]
  unfold readRulers
  dsimp only
  split
  · rename_i hC
    have hOld := (BinarySeedCursorMeasured.consume_data choiceRuler seed).symm.trans hC
    simp only [referenceTrace,hOld,BinarySeedCursorMeasured.consume_trace]
  · rename_i first hC
    have hOld := (BinarySeedCursorMeasured.consume_data choiceRuler seed).symm.trans hC
    simp only [referenceTrace,hOld,BinarySeedCursorMeasured.consume_trace]
    split
    · rename_i hS
      have hOldS := (BinarySeedCursorMeasured.consume_data precisionRuler first.2).symm.trans hS
      simp only [hOldS,BinarySeedCursorMeasured.consume_trace]
    · rename_i second hS
      have hOldS := (BinarySeedCursorMeasured.consume_data precisionRuler first.2).symm.trans hS
      simp only [hOldS,BinarySeedCursorMeasured.consume_trace]
      split
      · rename_i hO
        have hOldO := (BinarySeedCursorMeasured.consume_data precisionRuler second.2).symm.trans hO
        simp only [hOldO,BinarySeedCursorMeasured.consume_trace]
      · rename_i third hO
        have hOldO := (BinarySeedCursorMeasured.consume_data precisionRuler second.2).symm.trans hO
        simp only [hOldO,BinarySeedCursorMeasured.consume_trace]
        split <;> simp_all only [ite_true,ite_false]

theorem readRulers_work (n K : ℕ) (choiceRuler precisionRuler seed : List Bool)
    (hc : choiceRuler.length = coinBitBudget n K) (hp : precisionRuler.length = K) :
    (readRulers n K choiceRuler precisionRuler seed hc hp).2 ≤ 8*sampleBitBudget n K+20 := by
  have hN : sampleBitBudget n K = coinBitBudget n K+K+K := by unfold sampleBitBudget innerBitBudget; rfl
  have hC := BinarySeedCursorMeasured.consume_bound choiceRuler seed
  unfold readRulers
  dsimp only
  split
  · omega
  · rename_i first hFirst
    have hS := BinarySeedCursorMeasured.consume_bound precisionRuler first.2
    split
    · omega
    · rename_i second hSecond
      have hO := BinarySeedCursorMeasured.consume_bound precisionRuler second.2
      split
      · omega
      · split <;> omega

def read {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (Option (Blocks n prepared.request.precision) × Trace) × ℕ :=
  readRulers n prepared.request.precision prepared.choiceRuler prepared.precisionRuler seed
    prepared.choiceRuler_length prepared.precisionRuler_length

theorem read_erases {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (read prepared seed).1 = BinaryPRGBooleanSeedBlocks.readWithTrace prepared seed :=
  Prod.ext (readRulers_data _ _ _ _ _ _ _) (readRulers_trace _ _ _ _ _ _ _)

theorem read_work {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (read prepared seed).2 ≤ 8*sampleBitBudget n prepared.request.precision+20 :=
  readRulers_work _ _ _ _ _ _ _

def prepare {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (Option (Blocks n prepared.request.precision × (BinarySeedLookupTree.Store × Trace)) × Trace) × ℕ :=
  let blocks := read prepared seed
  match blocks.1.1 with
  | none => ((none,blocks.1.2),blocks.2+4)
  | some tapes =>
      let store := BinaryWordStoreMeasured.prepare tapes.choice.bits
      ((some (tapes,store.1),blocks.1.2),blocks.2+store.2+6)

theorem prepare_erases {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (prepare prepared seed).1 =
      (((BinaryPRGBooleanSeedBlocks.readWithTrace prepared seed).1.map
        (fun tapes => (tapes,BinaryWordStoreLifetime.prepareWithTrace tapes.choice.bits))),
        (BinaryPRGBooleanSeedBlocks.readWithTrace prepared seed).2) := by
  unfold prepare
  dsimp only
  rw [read_erases]
  cases h : (BinaryPRGBooleanSeedBlocks.readWithTrace prepared seed).1 with
  | none => rfl
  | some tapes => simp only [Option.map_some,BinaryWordStoreMeasured.prepare_erases]

theorem prepare_data {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (prepare prepared seed).1.1.map (fun held => (held.1,held.2.1)) =
      BinaryPRGSeedPreparationWork.tracedResult prepared seed := by
  rw [prepare_erases]
  simp only [Option.map_map,BinaryPRGSeedPreparationWork.tracedResult]
  rfl

theorem prepare_bound {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (prepare prepared seed).2 ≤ 42*sampleBitBudget n prepared.request.precision+40 := by
  have hb := read_work prepared seed
  unfold prepare
  dsimp only
  split
  · omega
  · rename_i tapes hTapes
    have hStore := BinaryWordStoreMeasured.prepare_bound tapes.choice.bits
    have hChoice := tapes.choice.size
    have hN : coinBitBudget n prepared.request.precision ≤
        sampleBitBudget n prepared.request.precision := by
      unfold sampleBitBudget innerBitBudget
      omega
    omega

end Blotto.BinarySeedPreparationMeasured
