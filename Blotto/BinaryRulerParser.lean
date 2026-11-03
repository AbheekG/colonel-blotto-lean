import Blotto.BinaryRequestRulerPlan
import Blotto.BinaryAllPayloadParser

/-! The selected physical request parser consumes actual accuracy and request
ruler plans. Forgetting only new ruler emission preserves the whole preceding
record and both earlier parser counters on every success or failure path. -/
namespace Blotto.BinaryRulerParser
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGFrame BinaryPRGHeaderFrame
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryAllPayloadParser (checkedGame)
set_option autoImplicit false
set_option maxHeartbeats 4000000

def read (frame : List Bool) : (((Option ((Σ n,Request n) × List Bool) × Trace) × ℕ) × ℕ) × (ℕ × ℕ) :=
  let supplied := checkedGame frame
  let produced := supplied.1
  let game := produced.1
  match game.1.1 with
  | none => ((((none,wrap 16 2 [game.1.2]),game.2+4),produced.2),(supplied.2,0))
  | some parsed =>
      let accuracyProduced := BinaryRequestRulerPlan.accuracyRead parsed.2
      let accuracy := accuracyProduced.1
      match accuracy.1.1 with
      | none => ((((none,wrap 48 2 [game.1.2,accuracy.1.2]),game.2+accuracy.2+8),produced.2),(supplied.2+accuracyProduced.2.1,accuracyProduced.2.2))
      | some selected =>
          let checked := parsed.1.2.prepared
          let assembledProduced := BinaryRequestRulerPlan.assembleWithEmission
            (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical checked)
            selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length
          let assembled := assembledProduced.1
          let physical : Request parsed.1.1 := ⟨assembled.1.1,checked.1,rfl⟩
          ((((some (⟨parsed.1.1,physical⟩,selected.2),wrap 64 2 [game.1.2,accuracy.1.2,assembled.1.2]),
            game.2+accuracy.2+assembled.2+16),produced.2),(supplied.2+accuracyProduced.2.1,accuracyProduced.2.2+assembledProduced.2))

theorem read_compat (frame : List Bool) :
    ((read frame).1,(read frame).2.1) = BinaryAllPayloadParser.read frame := by
  have ha (bits : List Bool) := BinaryRequestRulerPlan.accuracyRead_compat bits
  have hData (bits : List Bool) : (BinaryRequestRulerPlan.accuracyRead bits).1 =
      (BinaryHeaderAccuracyPayloadPlan.accuracy bits).1 := congrArg Prod.fst (ha bits)
  have hPrice (bits : List Bool) : (BinaryRequestRulerPlan.accuracyRead bits).2.1 =
      (BinaryHeaderAccuracyPayloadPlan.accuracy bits).2 := congrArg Prod.snd (ha bits)
  simp only [read,BinaryAllPayloadParser.read,hData,hPrice,
    BinaryRequestRulerPlan.assembleWithEmission_compat]
  cases hg : (checkedGame frame).1.1.1.1 with
  | none => simp only [hg]
  | some parsed =>
      simp only [hg]
      cases ha : (BinaryHeaderAccuracyPayloadPlan.accuracy parsed.2).1.1.1 <;> simp only [ha]

theorem read_previous (frame : List Bool) :
    (read frame).1.1 = BinaryPRGPhysicalRawRequestMeasured.read frame :=
  (congrArg (fun out => out.1.1) (read_compat frame)).trans (BinaryAllPayloadParser.read_previous frame)

theorem read_price (frame : List Bool) : (read frame).2.2 ≤ 30*(read frame).1.1.2 := by
  unfold read
  dsimp only
  split
  · dsimp only; omega
  · rename_i parsed hg
    have ha := BinaryRequestRulerPlan.accuracyRead_price parsed.2
    split
    · dsimp only; omega
    · rename_i selected hs
      have hp := BinaryRequestRulerPlan.assembleWithEmission_price
        (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical parsed.1.2.prepared)
        selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length
      dsimp only
      omega

theorem uniform_price : ∃ C d : ℕ,∀ frame : List Bool,(read frame).2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := BinaryPRGPhysicalRawRequestMeasured.uniform_joint
  refine ⟨30*C,d,?_⟩
  intro frame
  have hp := read_price frame
  rw [read_previous] at hp
  have ho := h frame
  nlinarith only [hp,ho]

end Blotto.BinaryRulerParser
