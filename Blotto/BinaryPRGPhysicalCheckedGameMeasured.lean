import Blotto.BinaryPRGCheckedPhysicalPreparationBounds

/-! Actual measured game parsing and ordered checked physical preparation
return one retained checked game. Malformed games skip checking; failed
promises skip numerical allocation. Exact old physical objects/traces and
frame-only source bounds are preserved; native model joins remain separate. -/
namespace Blotto.BinaryPRGPhysicalCheckedGameMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalCheckedGameLifetime (Checked)
set_option autoImplicit false

def read (frame : List Bool) : (Option ((Σ n,Checked n) × List Bool) × Trace) × ℕ :=
  let game := BinaryPRGGameFrameMeasured.read frame
  match game.1.1 with
  | none => ((none,wrap 16 2 [game.1.2]),game.2+4)
  | some parsed =>
      let checked := BinaryPRGCheckedPhysicalPreparationMeasured.checked parsed.1.2.game.input
        parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback
      let result := checked.1.1.map (fun prepared =>
        (⟨parsed.1.1,⟨prepared,parsed.1.2.header,parsed.1.2.rows,parsed.1.2.rows_length⟩⟩,parsed.2))
      ((result,wrap 48 2 [game.1.2,checked.1.2]),game.2+checked.2+8)

theorem read_erases (frame : List Bool) :
    (read frame).1 = BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame := by
  unfold read BinaryPRGPhysicalCheckedGameLifetime.readWithTrace
  dsimp only
  simp only [BinaryPRGGameFrameMeasured.read_erases,BinaryPRGCheckedPhysicalPreparationMeasured.checked_erases]
  cases (BinaryPRGGameFrameLifetime.readWithTrace frame).1 <;> rfl

def price (L : ℕ) : ℕ := 5000000000*(L+4)^5

theorem read_work (frame : List Bool) : (read frame).2 ≤ price frame.length := by
  have hGame := (BinaryPRGGameFrameMeasured.read_work frame).trans
    (BinaryPRGGameFrameMeasured.price_polynomial frame.length)
  have hX : 0 < frame.length+4 := by omega
  have hPow : (frame.length+1)^3 ≤ (frame.length+4)^5 :=
    (Nat.pow_le_pow_left (by omega : frame.length+1 ≤ frame.length+4) 3).trans
      (Nat.pow_le_pow_right hX (by decide : 3 ≤ 5))
  have hGameTop := hGame.trans (Nat.mul_le_mul_left 10000 hPow)
  have hOne : 1 ≤ (frame.length+4)^5 := Nat.one_le_pow 5 _ (by omega)
  unfold read
  dsimp only
  split
  · unfold price
    omega
  · rename_i parsed hParsed
    have hChecked := BinaryPRGCheckedPhysicalPreparationBounds.checked_raw_work frame parsed hParsed
    unfold price
    omega

theorem read_suffix_length (frame : List Bool) (parsed : (Σ n,Checked n) × List Bool)
    (hParsed : (read frame).1.1 = some parsed) : parsed.2.length ≤ frame.length :=
  BinaryPRGPhysicalRawRequestLifetime.physical_game_suffix_length frame parsed
    ((congrArg Prod.fst (read_erases frame)).symm.trans hParsed)

theorem read_dimension_bound (frame : List Bool) (parsed : (Σ n,Checked n) × List Bool)
    (hParsed : (read frame).1.1 = some parsed) : parsed.1.1 ≤ frame.length :=
  BinaryPRGPhysicalRawRequestLifetime.physical_game_dimension_bound frame parsed
    ((congrArg Prod.fst (read_erases frame)).symm.trans hParsed)

theorem read_usage (frame : List Bool) :
    usage (read frame).1.2 ≤ BinaryPRGPhysicalCheckedGameLifetime.envelope frame.length := by
  rw [read_erases]
  exact BinaryPRGPhysicalCheckedGameLifetime.readWithTrace_usage frame

theorem returned_stores_readback (frame : List Bool) (parsed : (Σ n,Checked n) × List Bool)
    (hParsed : (read frame).1.1 = some parsed) (index : List Bool) (j : Fin parsed.1.1)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace parsed.1.2.prepared.1.lengthStore index).1 =
        some (parsed.1.2.prepared.1.numerical.lengths.read j) ∧
      (BinaryWordObjectArrayAccess.getWithTrace parsed.1.2.prepared.1.poorStore index).1 =
        some (parsed.1.2.prepared.1.numerical.poorResources.read j) :=
  BinaryPRGPhysicalCheckedGameLifetime.returned_stores_readback frame parsed
    ((congrArg Prod.fst (read_erases frame)).symm.trans hParsed) index j hIndex

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (read frame).1.2 steps ≤
      borrowed+frame.length+BinaryPRGPhysicalCheckedGameLifetime.envelope frame.length ∧
    framePeak ((read frame).1.2.take steps) ≤ BinaryPRGPhysicalCheckedGameLifetime.envelope frame.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (read_usage frame) _ steps

end Blotto.BinaryPRGPhysicalCheckedGameMeasured
