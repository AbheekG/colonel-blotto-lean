import Blotto.BinaryGamePayloadPlan
import Blotto.BinaryPRGPhysicalRawRequestMeasured

/-! The selected physical parser consumes planned canonical payloads through
the actual game/checked-preparation/accuracy/assembly path. The complete old
request/trace/source record is exact. Other leaf and native scopes remain. -/
namespace Blotto.BinaryPhysicalPayloadPlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalCheckedGameLifetime (Checked)
open BinaryPRGPhysicalRawRequestLifetime (Request)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def checkedGame (frame : List Bool) : ((Option ((Σ n,Checked n) × List Bool) × Trace) × ℕ) × ℕ :=
  let produced := BinaryGamePayloadPlan.read frame
  let game := produced.1
  match game.1.1 with
  | none => (((none,wrap 16 2 [game.1.2]),game.2+4),produced.2)
  | some parsed =>
      let checked := BinaryPRGCheckedPhysicalPreparationMeasured.checked parsed.1.2.game.input
        parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback
      let result := checked.1.1.map (fun prepared =>
        (⟨parsed.1.1,⟨prepared,parsed.1.2.header,parsed.1.2.rows,parsed.1.2.rows_length⟩⟩,parsed.2))
      (((result,wrap 48 2 [game.1.2,checked.1.2]),game.2+checked.2+8),produced.2)

theorem checked_compat (frame : List Bool) :
    (checkedGame frame).1 = BinaryPRGPhysicalCheckedGameMeasured.read frame := by
  simp only [checkedGame,BinaryPRGPhysicalCheckedGameMeasured.read,BinaryGamePayloadPlan.read_compat]
  cases hGame : (BinaryPRGGameFrameMeasured.read frame).1.1 <;> simp only [hGame]

theorem checked_price (frame : List Bool) : (checkedGame frame).2 ≤ 30*(checkedGame frame).1.2 := by
  have h := BinaryGamePayloadPlan.read_price frame
  unfold checkedGame
  dsimp only
  split <;> dsimp only <;> omega

def read (frame : List Bool) : ((Option ((Σ n,Request n) × List Bool) × Trace) × ℕ) × ℕ :=
  let produced := checkedGame frame
  let game := produced.1
  match game.1.1 with
  | none => (((none,wrap 16 2 [game.1.2]),game.2+4),produced.2)
  | some parsed =>
      let accuracy := BinaryAccuracyMeasured.read parsed.2
      match accuracy.1.1 with
      | none => (((none,wrap 48 2 [game.1.2,accuracy.1.2]),game.2+accuracy.2+8),produced.2)
      | some selected =>
          let checked := parsed.1.2.prepared
          let assembled := BinaryPRGRequestRulersMeasured.assembleWithRows
            (BinaryPRGCheckedPhysicalPreparationLifetime.forgetPhysical checked)
            selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length
          let physical : Request parsed.1.1 := ⟨assembled.1.1,checked.1,rfl⟩
          (((some (⟨parsed.1.1,physical⟩,selected.2),wrap 64 2 [game.1.2,accuracy.1.2,assembled.1.2]),
            game.2+accuracy.2+assembled.2+16),produced.2)

theorem read_compat (frame : List Bool) : (read frame).1 = BinaryPRGPhysicalRawRequestMeasured.read frame := by
  simp only [read,BinaryPRGPhysicalRawRequestMeasured.read,checked_compat]
  cases hGame : (BinaryPRGPhysicalCheckedGameMeasured.read frame).1.1 with
  | none => simp only [hGame]
  | some parsed =>
      simp only [hGame]
      cases hAccuracy : (BinaryAccuracyMeasured.read parsed.2).1.1 <;> simp only [hAccuracy]

theorem read_original (frame : List Bool) :
    (read frame).1.1 = BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame :=
  (congrArg Prod.fst (read_compat frame)).trans (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)

theorem read_price (frame : List Bool) : (read frame).2 ≤ 30*(read frame).1.2 := by
  have h := checked_price frame
  unfold read
  dsimp only
  split
  · dsimp only; omega
  · split <;> dsimp only <;> omega

def cost (frame : List Bool) : ℕ := (read frame).1.2+(read frame).2

theorem cost_uniform : ∃ C d : ℕ,∀ frame : List Bool,cost frame ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryPRGPhysicalRawRequestMeasured.uniform_joint
  refine ⟨31*C,d,?_⟩
  intro frame
  have hp := read_price frame
  have ho := hOld frame
  rw [read_compat] at hp
  simp only [cost,read_compat]
  nlinarith only [ho,hp]

end Blotto.BinaryPhysicalPayloadPlan
