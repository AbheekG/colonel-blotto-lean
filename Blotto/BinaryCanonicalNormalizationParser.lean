import Blotto.BinaryCanonicalRowContinuation
import Blotto.BinaryCanonicalNormalizationReader
import Blotto.BinaryStoredRowParser

/-! The concrete planned canonical reader now reaches budgets and every stored
row word of the complete physical parser. Reusable row recursion preserves the
whole prior plan and emission price. All old parser counters remain exact. -/
namespace Blotto.BinaryCanonicalNormalizationParser
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGFrame BinaryPRGHeaderFrame
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def canonicalBackend : BinaryCanonicalRowContinuation.Backend ℕ where
  run := BinaryCanonicalNormalizationReader.read
  compat := BinaryCanonicalNormalizationReader.read_compat

def row (counter bits : List Bool) := BinaryCanonicalRowContinuation.row canonicalBackend counter bits

theorem row_compat (counter bits : List Bool) : (row counter bits).1 = BinaryStoredRowPlan.row counter bits :=
  BinaryCanonicalRowContinuation.row_compat canonicalBackend counter bits

theorem row_price (counter bits : List Bool) :
    (row counter bits).2 ≤ 4*(row counter bits).1.1.1.2+25*(row counter bits).1.1.1.1.2.length+5 :=
  BinaryCanonicalRowContinuation.row_price canonicalBackend BinaryCanonicalNormalizationReader.read_price counter bits

def game (bits : List Bool) : ((((((Option ((Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool) × Trace) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let control := BinaryHeaderControlReaders.header bits
  let supplied := control.1
  let dimension := supplied.1
  let returned :=
    match dimension.1.1 with
    | none => (((((none,wrap 16 2 [dimension.1.2]),dimension.2+4),0),0),0)
    | some raw =>
        let firstExtended := BinaryCanonicalNormalizationReader.read raw.2
        let firstProduced := firstExtended.1
        let first := firstProduced.1
        match first.1.1 with
        | none => (((((none,wrap 24 2 [dimension.1.2,first.1.2]),dimension.2+first.2+8),firstProduced.2),0),firstExtended.2)
        | some firstWord =>
            let secondExtended := BinaryCanonicalNormalizationReader.read firstWord.2
            let secondProduced := secondExtended.1
            let second := secondProduced.1
            match second.1.1 with
            | none => (((((none,wrap 32 2 [dimension.1.2,first.1.2,second.1.2]),dimension.2+first.2+second.2+12),firstProduced.2+secondProduced.2),0),firstExtended.2+secondExtended.2)
            | some secondWord =>
                let rowExtended := row raw.1.payload secondWord.2
                let rowProduced := rowExtended.1
                let wordsProduced := rowProduced.1
                let words := wordsProduced.1
                match words.1.1 with
                | none => (((((none,wrap 40 2 [dimension.1.2,first.1.2,second.1.2,words.1.2]),
                    dimension.2+first.2+second.2+words.2+16),firstProduced.2+secondProduced.2+wordsProduced.2),rowProduced.2),firstExtended.2+secondExtended.2+rowExtended.2)
                | some rest =>
                    let packed := BinaryPRGGameFrameMeasured.pack raw.1.typed firstWord.1 secondWord.1 rest
                    (((((some packed.1.1,wrap 80 (raw.1.payload.length+8)
                      [dimension.1.2,first.1.2,second.1.2,words.1.2,packed.1.2]),
                      dimension.2+first.2+second.2+words.2+packed.2+20),firstProduced.2+secondProduced.2+wordsProduced.2),rowProduced.2),firstExtended.2+secondExtended.2+rowExtended.2)
  ((((returned.1.1,supplied.2),control.2),returned.1.2),returned.2)

theorem game_compat (bits : List Bool) : (game bits).1 = BinaryStoredRowParser.game bits := by
  simp only [game,BinaryStoredRowParser.game,BinaryCanonicalNormalizationReader.read_compat,row_compat]
  cases hd : (BinaryHeaderControlReaders.header bits).1.1.1.1 with
  | none => simp only [hd]
  | some raw =>
      simp only [hd]
      cases hf : (BinaryCanonicalPayloadPlan.read raw.2).1.1.1 with
      | none => simp only [hf]
      | some first =>
          simp only [hf]
          cases hs : (BinaryCanonicalPayloadPlan.read first.2).1.1.1 with
          | none => simp only [hs]
          | some second =>
              simp only [hs]
              cases hr : (BinaryStoredRowPlan.row raw.1.payload second.2).1.1.1.1 <;> simp only [hr]

theorem game_price (bits : List Bool) :
    (game bits).2 ≤ 4*(game bits).1.1.1.1.1.2+25*(game bits).1.1.1.1.1.1.2.length+5 := by
  unfold game
  dsimp only
  split
  · dsimp only; omega
  · rename_i raw hd
    have hf := BinaryCanonicalNormalizationReader.read_price raw.2
    split
    · dsimp only
      simp only [wrap,combine,List.length_append,List.length_cons,List.length_nil,under_length]
      omega
    · rename_i first hFirst
      have hs := BinaryCanonicalNormalizationReader.read_price first.2
      split
      · dsimp only
        simp only [wrap,combine,List.length_append,List.length_cons,List.length_nil,under_length]
        omega
      · rename_i second hSecond
        have hr := row_price raw.1.payload second.2
        split <;> dsimp only <;>
          simp only [wrap,combine,List.length_append,List.length_cons,List.length_nil,under_length] <;> omega

def checkedGame (frame : List Bool) : ((((((Option ((Σ n,BinaryPRGPhysicalCheckedGameLifetime.Checked n) × List Bool) × Trace) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let extended := game frame
  let producedRow := extended.1
  let control := producedRow.1
  let supplied := control.1
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
  ((((returned,supplied.2),control.2),producedRow.2),extended.2)

theorem checked_compat (frame : List Bool) : (checkedGame frame).1 = BinaryStoredRowParser.checkedGame frame := by
  simp only [checkedGame,BinaryStoredRowParser.checkedGame,game_compat]
  rfl

theorem checked_price (frame : List Bool) :
    (checkedGame frame).2 ≤ 4*(checkedGame frame).1.1.1.1.1.2+25*(checkedGame frame).1.1.1.1.1.1.2.length+5 := by
  have h := game_price frame
  unfold checkedGame
  dsimp only
  split <;> dsimp only <;>
    simp only [wrap,combine,List.length_append,List.length_cons,List.length_nil,under_length] <;> omega

def read (frame : List Bool) : (((Option ((Σ n,Request n) × List Bool) × Trace) × ℕ) × ℕ) × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :=
  let extended := checkedGame frame
  let producedRow := extended.1
  let control := producedRow.1
  let supplied := control.1
  let produced := supplied.1
  let game := produced.1
  let returned : (((Option ((Σ n,Request n) × List Bool) × Trace) × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) :=
    match game.1.1 with
    | none => ((((none,wrap 16 2 [game.1.2]),game.2+4),produced.2),((supplied.2,0),control.2))
    | some parsed =>
        let accuracyControl := BinaryHeaderControlReaders.accuracy parsed.2
        let accuracyProduced := accuracyControl.1
        let accuracy := accuracyProduced.1
        match accuracy.1.1 with
        | none => ((((none,wrap 48 2 [game.1.2,accuracy.1.2]),game.2+accuracy.2+8),produced.2),((supplied.2+accuracyProduced.2.1,accuracyProduced.2.2),control.2+accuracyControl.2))
        | some selected =>
            let checked := parsed.1.2.prepared
            let assembledProduced := BinaryRequestRulerPlan.assembleWithEmission
              (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical checked)
              selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length
            let assembled := assembledProduced.1
            let physical : Request parsed.1.1 := ⟨assembled.1.1,checked.1,rfl⟩
            ((((some (⟨parsed.1.1,physical⟩,selected.2),wrap 64 2 [game.1.2,accuracy.1.2,assembled.1.2]),
              game.2+accuracy.2+assembled.2+16),produced.2),((supplied.2+accuracyProduced.2.1,accuracyProduced.2.2+assembledProduced.2),control.2+accuracyControl.2))
  (returned.1,((returned.2,producedRow.2),extended.2))

theorem read_compat (frame : List Bool) :
    ((read frame).1,(read frame).2.1) = BinaryStoredRowParser.read frame := by
  simp only [read,BinaryStoredRowParser.read,checked_compat]
  rfl

theorem read_previous (frame : List Bool) :
    (read frame).1.1 = BinaryPRGPhysicalRawRequestMeasured.read frame :=
  (congrArg (fun out => out.1.1) (read_compat frame)).trans (BinaryStoredRowParser.read_previous frame)

theorem read_price (frame : List Bool) :
    (read frame).2.2 ≤ 4*(read frame).1.1.2+25*(read frame).1.1.1.2.length+5 := by
  have h := checked_price frame
  unfold read
  dsimp only
  split
  · dsimp only
    simp only [wrap,combine,List.length_append,List.length_cons,List.length_nil,under_length]
    omega
  · split <;> dsimp only <;>
      simp only [wrap,combine,List.length_append,List.length_cons,List.length_nil,under_length] <;> omega

theorem uniform_price : ∃ C d : ℕ,∀ frame : List Bool,(read frame).2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSource⟩ := BinaryPRGPhysicalRawRequestMeasured.uniform_joint
  obtain ⟨P,e,hTrace⟩ := BinaryPhysicalParserTraceSparsity.uniform_parser_length
  refine ⟨4*C+25*P+5,max d e,?_⟩
  intro frame
  have hp := read_price frame
  rw [read_previous] at hp
  rw [congrArg Prod.snd (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)] at hp
  have hs := hSource frame
  have ht := hTrace frame
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hOne := Nat.one_le_pow (max d e) (frame.length+1) (by omega)
  nlinarith only [hp,hs,ht,hd,he,hOne]

end Blotto.BinaryCanonicalNormalizationParser
