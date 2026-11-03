import Blotto.RationalTerminalGroupInputs
import Blotto.RationalGroupPrograms
import Blotto.PreparedGroupOutput
import Blotto.RationalCachedGroupSpecs

/-! A terminal Lotto vector compiles its groups, retained route table and
selected coupling controller. Every controller output and fallback spends B.
The cap covers the selected local continuation, without nested sampler calls. -/

namespace Blotto.RationalTerminalLotto

def programReference {n : ℕ} (i : RationalTerminalLotto n) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    RationalAllocationProgram n 80 :=
  let output := PreparedGroupOutput.prepare i.partition
  match h : i.pivot with
  | none =>
    (((i.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits).mapped
      (fun y => (output.emit y).allocation)).widen (by decide)
  | some pivot =>
    ((i.mixedSpec pivot (i.pivot_some h)).program i.groups_count K outerBits scalarBits).mapped
      (fun y => (output.emitMixed pivot y).allocation)

def program {n : ℕ} (i : RationalTerminalLotto n) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    RationalAllocationProgram n 80 :=
  let packed := RationalTerminalPacking.prepare i
  let output := packed.prepareOutput
  match h : i.pivot with
  | none =>
    (((packed.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits).mapped
      (fun y => (output.emit y).allocation)).widen (by decide)
  | some pivot =>
    ((packed.mixedSpec pivot (i.pivot_some h)).program i.groups_count K outerBits scalarBits).mapped
      (fun y => (output.emitMixed pivot y).allocation)

theorem program_refines {n : ℕ} (i : RationalTerminalLotto n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) :
    i.program K outerBits scalarBits = i.programReference K outerBits scalarBits := by
  have hEmit : (fun y => ((RationalTerminalPacking.prepare i).prepareOutput.emit y).allocation) =
      (fun y => ((PreparedGroupOutput.prepare i.partition).emit y).allocation) := by
    funext y
    rw [PreparedGroupOutput.emit_allocation, PreparedGroupOutput.emit_allocation]
  have hMixed : ∀ pivot,
      (fun y => ((RationalTerminalPacking.prepare i).prepareOutput.emitMixed pivot y).allocation) =
      (fun y => ((PreparedGroupOutput.prepare i.partition).emitMixed pivot y).allocation) := by
    intro pivot
    funext y
    rw [PreparedGroupOutput.emitMixed_allocation, PreparedGroupOutput.emitMixed_allocation]
  unfold program programReference
  dsimp only
  split <;> simp only [RationalTerminalPacking.uniformSpec_eq,
    RationalTerminalPacking.mixedSpec_eq, hEmit, hMixed]

theorem program_leavesBudget {n : ℕ} (i : RationalTerminalLotto n) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    (i.program K outerBits scalarBits).LeavesBudget i.B := by
  rw [program_refines]
  unfold programReference
  dsimp only
  split
  · rename_i h
    change (((i.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits).mapped
      (fun y => ((PreparedGroupOutput.prepare i.partition).emit y).allocation)).LeavesBudget i.B
    exact RationalAllocationProgram.mapped_leavesBudget _ _
      ((i.uniformSpec (i.pivot_none h)).program_leavesBudget i.groups_count K scalarBits)
      (fun y hy => (PreparedGroupOutput.prepare i.partition).emit_fullBudget hy)
  · rename_i pivot h
    exact RationalAllocationProgram.mapped_leavesBudget _ _
      ((i.mixedSpec pivot (i.pivot_some h)).program_leavesBudget i.groups_count K outerBits scalarBits)
      (fun y hy => (PreparedGroupOutput.prepare i.partition).emitMixed_fullBudget pivot hy)

theorem program_sample_fullBudget {n : ℕ} (i : RationalTerminalLotto n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    FullBudget (i.B : ℝ) (fun j => ((i.program K outerBits scalarBits).sample R choiceBits j : ℝ)) :=
  (i.program K outerBits scalarBits).sample_fullBudget (i.program_leavesBudget K outerBits scalarBits) R choiceBits

end Blotto.RationalTerminalLotto
