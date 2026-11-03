import Blotto.BinaryPromiseOpcodePreparation
import Blotto.BinaryNumericalOpcodeParser

/-! Ordered promise guards, sums and normalization now use one planned trace
emission before numerical preparation. Every prior parser record/price remains
exact; reached promise division/emission is an additional returned price. -/
namespace Blotto.BinaryPromiseOpcodeParser
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGFrame BinaryPRGHeaderFrame
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryResourceTraceLength (under_length)
open BinaryCanonicalNormalizationParser (game)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def checkedGame (frame : List Bool) : ((((((((Option ((Σ n,BinaryPRGPhysicalCheckedGameLifetime.Checked n) × List Bool) × Trace) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let extended := game frame
  let producedRow := extended.1
  let control := producedRow.1
  let supplied := control.1
  let produced := supplied.1
  let game := produced.1
  let returned :=
    match game.1.1 with
    | none => (((((none,wrap 16 2 [game.1.2]),game.2+4),produced.2),0),0)
    | some parsed =>
        let promised := BinaryPromiseOpcodePreparation.checked parsed.1.2.game.input
          parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback
        let numeric := promised.1
        let checked := numeric.1
        let result : Option ((Σ n,BinaryPRGPhysicalCheckedGameLifetime.Checked n) × List Bool) := checked.1.1.map (fun prepared =>
          (⟨parsed.1.1,⟨prepared,parsed.1.2.header,parsed.1.2.rows,parsed.1.2.rows_length⟩⟩,parsed.2))
        (((((result,wrap 48 2 [game.1.2,checked.1.2]),game.2+checked.2+8),produced.2),numeric.2),promised.2)
  ((((((returned.1.1,supplied.2),control.2),producedRow.2),extended.2),returned.1.2),returned.2)

theorem checked_compat (frame : List Bool) :
    (checkedGame frame).1 = BinaryNumericalOpcodeParser.checkedGame frame := by
  simp only [checkedGame,BinaryNumericalOpcodeParser.checkedGame,BinaryPromiseOpcodePreparation.checked_compat]
  cases hg : (game frame).1.1.1.1.1.1.1 with
  | none => simp only [hg]
  | some parsed => simp only [hg]

theorem checked_price (frame : List Bool) :
    (checkedGame frame).2 ≤ 4*(checkedGame frame).1.1.1.1.1.1.1.2+
      25*(checkedGame frame).1.1.1.1.1.1.1.1.2.length+5 := by
  unfold checkedGame
  dsimp only
  split
  · dsimp only; omega
  · rename_i parsed hs
    have hp := BinaryPromiseOpcodePreparation.checked_price parsed.1.2.game.input parsed.1.2.game.canonical
      parsed.1.2.rows parsed.1.2.rows_readback
    dsimp only
    simp only [wrap,combine,List.length_append,List.length_cons,List.length_nil,under_length]
    omega

def read (frame : List Bool) : (((Option ((Σ n,Request n) × List Bool) × Trace) × ℕ) × ℕ) × ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) :=
  let promise := checkedGame frame
  let numeric := promise.1
  let extended := numeric.1
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
  (returned.1,((((returned.2,producedRow.2),extended.2),numeric.2),promise.2))

theorem read_compat (frame : List Bool) :
    ((read frame).1,(read frame).2.1) = BinaryNumericalOpcodeParser.read frame := by
  simp only [read,BinaryNumericalOpcodeParser.read,checked_compat]
  rfl

theorem read_previous (frame : List Bool) :
    (read frame).1.1 = BinaryPRGPhysicalRawRequestMeasured.read frame :=
  (congrArg (fun out => out.1.1) (read_compat frame)).trans (BinaryNumericalOpcodeParser.read_previous frame)

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


end Blotto.BinaryPromiseOpcodeParser
