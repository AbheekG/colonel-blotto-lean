import Blotto.BinaryHeaderAccuracyPayloadPlan
import Blotto.BinaryPhysicalPayloadPlan

/-! Every dimension, canonical-word and accuracy payload now consumes actual
plans. Full preceding records and canonical emissions are exact on forgetting
only dimension/accuracy emission. Other trace/native/space scopes remain. -/
namespace Blotto.BinaryAllPayloadParser
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGFrame BinaryPRGHeaderFrame
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalCheckedGameLifetime (Checked)
open BinaryPRGPhysicalRawRequestLifetime (Request)
set_option autoImplicit false
set_option maxHeartbeats 4000000

def game (bits : List Bool) : (((Option ((Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool) × Trace) × ℕ) × ℕ) × ℕ :=
  let supplied := BinaryHeaderAccuracyPayloadPlan.header bits
  let dimension := supplied.1
  let returned :=
    match dimension.1.1 with
    | none => (((none,wrap 16 2 [dimension.1.2]),dimension.2+4),0)
    | some raw =>
        let firstProduced := BinaryCanonicalPayloadPlan.read raw.2
        let first := firstProduced.1
        match first.1.1 with
        | none => (((none,wrap 24 2 [dimension.1.2,first.1.2]),dimension.2+first.2+8),firstProduced.2)
        | some firstWord =>
            let secondProduced := BinaryCanonicalPayloadPlan.read firstWord.2
            let second := secondProduced.1
            match second.1.1 with
            | none => (((none,wrap 32 2 [dimension.1.2,first.1.2,second.1.2]),dimension.2+first.2+second.2+12),firstProduced.2+secondProduced.2)
            | some secondWord =>
                let wordsProduced := BinaryGamePayloadPlan.row raw.1.payload secondWord.2
                let words := wordsProduced.1
                match words.1.1 with
                | none => (((none,wrap 40 2 [dimension.1.2,first.1.2,second.1.2,words.1.2]),
                    dimension.2+first.2+second.2+words.2+16),firstProduced.2+secondProduced.2+wordsProduced.2)
                | some rest =>
                    let packed := BinaryPRGGameFrameMeasured.pack raw.1.typed firstWord.1 secondWord.1 rest
                    (((some packed.1.1,wrap 80 (raw.1.payload.length+8)
                      [dimension.1.2,first.1.2,second.1.2,words.1.2,packed.1.2]),
                      dimension.2+first.2+second.2+words.2+packed.2+20),firstProduced.2+secondProduced.2+wordsProduced.2)
  (returned,supplied.2)

theorem game_compat (bits : List Bool) : (game bits).1 = BinaryGamePayloadPlan.read bits := by
  simp only [game,BinaryGamePayloadPlan.read,BinaryHeaderAccuracyPayloadPlan.header_compat]
  rfl

theorem game_price (bits : List Bool) : (game bits).2 ≤ 30*(game bits).1.1.2 := by
  have h := BinaryHeaderAccuracyPayloadPlan.header_price bits
  unfold game
  dsimp only
  split
  · dsimp only; omega
  · split
    · dsimp only; omega
    · split
      · dsimp only; omega
      · split <;> dsimp only <;> omega

def checkedGame (frame : List Bool) : (((Option ((Σ n,BinaryPRGPhysicalCheckedGameLifetime.Checked n) × List Bool) × Trace) × ℕ) × ℕ) × ℕ :=
  let supplied := game frame
  let produced := supplied.1
  let game := produced.1
  let returned :=
    match game.1.1 with
    | none => (((none,wrap 16 2 [game.1.2]),game.2+4),produced.2)
    | some parsed =>
        let checked := BinaryPRGCheckedPhysicalPreparationMeasured.checked parsed.1.2.game.input
          parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback
        let result := checked.1.1.map (fun prepared =>
          (⟨parsed.1.1,⟨prepared,parsed.1.2.header,parsed.1.2.rows,parsed.1.2.rows_length⟩⟩,parsed.2))
        (((result,wrap 48 2 [game.1.2,checked.1.2]),game.2+checked.2+8),produced.2)
  (returned,supplied.2)

theorem checked_compat (frame : List Bool) :
    (checkedGame frame).1 = BinaryPhysicalPayloadPlan.checkedGame frame := by
  simp only [checkedGame,BinaryPhysicalPayloadPlan.checkedGame,game_compat]
  rfl

theorem checked_price (frame : List Bool) :
    (checkedGame frame).2 ≤ 30*(checkedGame frame).1.1.2 := by
  have h := game_price frame
  unfold checkedGame
  dsimp only
  split <;> dsimp only <;> omega

def read (frame : List Bool) : (((Option ((Σ n,Request n) × List Bool) × Trace) × ℕ) × ℕ) × ℕ :=
  let supplied := checkedGame frame
  let produced := supplied.1
  let game := produced.1
  match game.1.1 with
  | none => ((((none,wrap 16 2 [game.1.2]),game.2+4),produced.2),supplied.2)
  | some parsed =>
      let accuracyProduced := BinaryHeaderAccuracyPayloadPlan.accuracy parsed.2
      let accuracy := accuracyProduced.1
      match accuracy.1.1 with
      | none => ((((none,wrap 48 2 [game.1.2,accuracy.1.2]),game.2+accuracy.2+8),produced.2),supplied.2+accuracyProduced.2)
      | some selected =>
          let checked := parsed.1.2.prepared
          let assembled := BinaryPRGRequestRulersMeasured.assembleWithRows
            (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical checked)
            selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length
          let physical : Request parsed.1.1 := ⟨assembled.1.1,checked.1,rfl⟩
          ((((some (⟨parsed.1.1,physical⟩,selected.2),wrap 64 2 [game.1.2,accuracy.1.2,assembled.1.2]),
            game.2+accuracy.2+assembled.2+16),produced.2),supplied.2+accuracyProduced.2)

theorem read_compat (frame : List Bool) : (read frame).1 = BinaryPhysicalPayloadPlan.read frame := by
  simp only [read,BinaryPhysicalPayloadPlan.read,checked_compat,BinaryHeaderAccuracyPayloadPlan.accuracy_compat]
  cases hg : (BinaryPhysicalPayloadPlan.checkedGame frame).1.1.1 with
  | none => simp only [hg]
  | some parsed =>
      simp only [hg]
      cases ha : (BinaryAccuracyMeasured.read parsed.2).1.1 <;> simp only [ha]

theorem read_previous (frame : List Bool) :
    (read frame).1.1 = BinaryPRGPhysicalRawRequestMeasured.read frame :=
  (congrArg Prod.fst (read_compat frame)).trans (BinaryPhysicalPayloadPlan.read_compat frame)

theorem read_price (frame : List Bool) : (read frame).2 ≤ 30*(read frame).1.1.2 := by
  have h := checked_price frame
  unfold read
  dsimp only
  split
  · dsimp only; omega
  · rename_i parsed hg
    have ha := BinaryHeaderAccuracyPayloadPlan.accuracy_price parsed.2
    split <;> dsimp only <;> omega

theorem uniform_price : ∃ C d : ℕ,∀ frame : List Bool,(read frame).2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := BinaryPRGPhysicalRawRequestMeasured.uniform_joint
  refine ⟨30*C,d,?_⟩
  intro frame
  have hp := read_price frame
  rw [read_previous] at hp
  have ho := h frame
  nlinarith only [hp,ho]

end Blotto.BinaryAllPayloadParser
