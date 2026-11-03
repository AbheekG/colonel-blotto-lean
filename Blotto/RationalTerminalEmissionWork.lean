import Blotto.RationalTerminalLottoHeight
import Blotto.RationalGroupEmissionBounds
import Blotto.PreparedGroupEmissionArithmetic

/-! The terminal compiler's actual packed route table prices output emission
on the selected group controller. Work is zero when the controller exhausts;
the paper-level fallback row and all small-vector production are separate. -/

namespace Blotto.RationalTerminalLotto

def emissionBitWork {n : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool)
    (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  let packed := RationalTerminalPacking.prepare i
  let output := packed.prepareOutput
  match h : i.pivot with
  | none =>
    let group := (packed.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits
    group.machine.cachedEmissionWork (output.emitBitCost model) N bits (.state group.start) pos hpos
  | some pivot =>
    let group := (packed.mixedSpec pivot (i.pivot_some h)).program i.groups_count K outerBits scalarBits
    group.machine.cachedEmissionWork (output.emitMixedBitCost model pivot) N bits (.state group.start) pos hpos

theorem OnLattice.emissionBitWork_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s) (model : RationalCostModel)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool)
    (pos : ℕ) (hpos : pos ≤ N) :
    i.emissionBitWork model K outerBits scalarBits N bits pos hpos ≤
      (4 + 8 * n) * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 75) := by
  let w := max s (K + 2)
  have hw : 2 ≤ w := hs.trans (le_max_left _ _)
  have hBudgetW := hBudget.mono (le_max_left s (K + 2))
  have hWidthW : binaryWordWidth D ≤ w := hWidth.trans (le_max_left _ _)
  let output := (RationalTerminalPacking.prepare i).prepareOutput
  have hCoefficient : ∀ j, RationalHeight (output.table.read j).2 w := fun j =>
    (output.coefficient_height_lattice D hD h.1 (fun j => (i.length_le j).trans hB)
      (fun g => (i.partition_total_le g).trans hB) j).mono hWidthW
  have hCount : i.groups.length ≤ 3 := by rcases i.groups_count with hc | hc <;> omega
  unfold emissionBitWork
  dsimp only
  split
  · rename_i hNone
    rw [RationalTerminalPacking.uniformSpec_eq]
    have hc := (h.uniformSpec hD hB w hBudgetW hWidthW (i.pivot_none hNone)).emissionWork_bound
      hw i.groups_count output hCoefficient model K scalarBits N bits pos hpos
    rw [max_eq_left (le_max_right s (K + 2))] at hc
    have hm := model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (expressionHeightBudget_mono w (by decide : 22 ≤ 75))) 1)
    exact hc.trans ((Nat.mul_le_mul_left _ hm).trans (Nat.mul_le_mul_right _ (by omega)))
  · rename_i pivot hSome
    rw [RationalTerminalPacking.mixedSpec_eq]
    have hm := expressionHeightBudget_ge_input w 1
    have hc := (h.mixedSpec hD hB w hBudgetW hWidthW pivot (i.pivot_some hSome)).emissionWork_bound
      (hw.trans hm) i.groups_count output pivot (fun j => (hCoefficient j).mono hm)
      model K outerBits scalarBits N bits pos hpos
    rw [max_eq_left ((le_max_right s (K + 2)).trans hm), expressionHeightBudget_comp] at hc
    exact hc.trans (Nat.mul_le_mul_right _ (by omega))

def emissionArithmeticWork {n : ℕ} (i : RationalTerminalLotto n) : ℕ :=
  let output := (RationalTerminalPacking.prepare i).prepareOutput
  match i.pivot with
  | none => output.emitArithmeticWork
  | some _ => output.emitMixedArithmeticWork

theorem emissionArithmeticWork_bound {n : ℕ} (i : RationalTerminalLotto n) :
    i.emissionArithmeticWork ≤ 2 * n := by
  unfold emissionArithmeticWork
  dsimp only
  split
  · have hc := (RationalTerminalPacking.prepare i).prepareOutput.emitArithmeticWork_bound
    omega
  · exact (RationalTerminalPacking.prepare i).prepareOutput.emitMixedArithmeticWork_bound

end Blotto.RationalTerminalLotto
