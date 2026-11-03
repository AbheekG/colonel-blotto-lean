import Blotto.RationalUnitLatticeHeight
import Blotto.RationalGroupProgramHeight
import Blotto.PreparedGroupHeight
import Blotto.RationalProgramHeight
import Blotto.RationalTerminalProgram

/-! The actual terminal partition, mixed probability and prepared output map
inherit the input denominator. This closes all terminal output-size branches. -/

namespace Blotto.RationalTerminalLotto

def OnLattice {n : ℕ} (i : RationalTerminalLotto n) (D : ℕ) : Prop :=
  (∀ j, OnRationalLattice D (i.length j)) ∧ ∀ j, OnRationalLattice D (i.resource j)

theorem OnLattice.length_height {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ} (h : i.OnLattice D)
    (hD : 0 < D) (hB : i.B ≤ 1) (j : Fin n) : RationalHeight (i.length j) (binaryWordWidth D) :=
  rationalHeight_unit_lattice hD (h.1 j) ⟨le_of_lt (i.length_pos j), (i.length_le j).trans hB⟩

theorem OnLattice.resource_height {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ} (h : i.OnLattice D)
    (hD : 0 < D) (hB : i.B ≤ 1) (j : Fin n) : RationalHeight (i.resource j) (binaryWordWidth D) :=
  rationalHeight_unit_lattice hD (h.2 j) ⟨(i.box j).1, ((i.box j).2.trans (i.length_le j)).trans hB⟩

theorem OnLattice.total_height {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ} (h : i.OnLattice D)
    (hD : 0 < D) (hB : i.B ≤ 1) (g : Fin i.groups.length) : RationalHeight (i.partition.total g) (binaryWordWidth D) :=
  rationalHeight_unit_lattice hD (i.partition.total_on_lattice D h.1 g)
    ⟨le_of_lt (i.partition.total_pos g), (i.partition_total_le g).trans hB⟩

theorem OnLattice.coefficient_height {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ} (h : i.OnLattice D)
    (hD : 0 < D) (hB : i.B ≤ 1) (j : Fin n) :
    RationalHeight ((PreparedGroupOutput.prepare i.partition).table.read j).2 (binaryWordWidth D) :=
  (PreparedGroupOutput.prepare i.partition).coefficient_height_lattice D hD h.1
    (fun j => (i.length_le j).trans hB) (fun g => (i.partition_total_le g).trans hB) j

theorem OnLattice.uniformSpec {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ} (h : i.OnLattice D)
    (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s)
    (hNo : ∀ j, ¬(0 < i.resource j ∧ i.resource j < i.length j)) :
    (i.uniformSpec hNo).FieldsHeight s := ⟨hBudget, fun g => (h.total_height hD hB g).mono hWidth⟩

theorem OnLattice.mixedSpec {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ} (h : i.OnLattice D)
    (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s)
    (pivot : Fin n) (hp : 0 < i.resource pivot ∧ i.resource pivot < i.length pivot) :
    (i.mixedSpec pivot hp).FieldsHeight (expressionHeightBudget s 1) := by
  have hLength : RationalHeight (i.length pivot) (expressionHeightBudget s 0) := by
    simpa only [expressionHeightBudget_zero] using (h.length_height hD hB pivot).mono hWidth
  have hResource : RationalHeight (i.resource pivot) (expressionHeightBudget s 0) := by
    simpa only [expressionHeightBudget_zero] using (h.resource_height hD hB pivot).mono hWidth
  have hm := expressionHeightBudget_ge_input s 1
  exact ⟨hBudget.mono hm, fun g => (h.total_height hD hB g).mono (hWidth.trans hm),
    (h.length_height hD hB pivot).mono (hWidth.trans hm), hResource.div_level hLength⟩

theorem OnLattice.program_leaves {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ} (h : i.OnLattice D)
    (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s) (hBudget : RationalHeight i.B s)
    (hWidth : binaryWordWidth D ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    (i.program K outerBits scalarBits).LeavesHeight (expressionHeightBudget (max s (K + 2)) 75) := by
  let w := max s (K + 2)
  have hw : 2 ≤ w := hs.trans (le_max_left _ _)
  have hBudgetW := hBudget.mono (le_max_left s (K + 2))
  have hWidthW : binaryWordWidth D ≤ w := hWidth.trans (le_max_left _ _)
  have hCoefficient := fun j => (h.coefficient_height hD hB j).mono hWidthW
  rw [program_refines]
  unfold RationalTerminalLotto.programReference
  dsimp only
  split
  · rename_i hNone
    change (((i.uniformSpec (i.pivot_none hNone)).program i.groups_count K scalarBits).mapped
      (fun y => ((PreparedGroupOutput.prepare i.partition).emit y).allocation)).LeavesHeight _
    have hGroup := (h.uniformSpec hD hB w hBudgetW hWidthW (i.pivot_none hNone)).program_leaves hw i.groups_count K scalarBits
    rw [max_eq_left (le_max_right s (K + 2))] at hGroup
    apply RationalAllocationProgram.mapped_leavesHeight _ _ _ _ hGroup
    intro y hy j
    have hOut := (PreparedGroupOutput.prepare i.partition).emit_of_coefficient_heights w _ (by omega) hCoefficient y hy j
    rw [max_eq_right (expressionHeightBudget_ge_input w 21), expressionHeightBudget_comp] at hOut
    exact hOut.mono (expressionHeightBudget_mono w (by decide : 22 ≤ 75))
  · rename_i pivot hSome
    have hm := expressionHeightBudget_ge_input w 1
    have hGroup := (h.mixedSpec hD hB w hBudgetW hWidthW pivot (i.pivot_some hSome)).program_leaves
      (hw.trans hm) i.groups_count K outerBits scalarBits
    rw [max_eq_left ((le_max_right s (K + 2)).trans hm), expressionHeightBudget_comp] at hGroup
    apply RationalAllocationProgram.mapped_leavesHeight _ _ _ _ hGroup
    intro y hy j
    have hOut := (PreparedGroupOutput.prepare i.partition).emitMixed_of_coefficient_heights w _ (by omega) hCoefficient pivot y hy j
    rw [max_eq_right (expressionHeightBudget_ge_input w 73), expressionHeightBudget_comp] at hOut
    exact hOut

end Blotto.RationalTerminalLotto
