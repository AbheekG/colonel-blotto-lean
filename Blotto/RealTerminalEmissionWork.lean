import Blotto.RealTerminalSampler
import Blotto.RealPreparedGroupEmissionWork

/-! The actual exact-real terminal branch uses one cached output coordinate
pass. These unit-price scalar/arithmetic components exclude the pivot scan,
packing, the group draw, addresses, allocation and physical ownership. -/

namespace Blotto.TerminalLotto

noncomputable def realEmissionScalarWork {n : ℕ} (i : TerminalLotto n) : ℕ :=
  let output := (RealTerminalPacking.prepare i).prepareOutput
  match i.realPivot with
  | none => output.emitScalarWork
  | some _ => output.emitMixedScalarWork

theorem realEmissionScalarWork_bound {n : ℕ} (i : TerminalLotto n) :
    i.realEmissionScalarWork ≤ 8 + 11 * n := by
  have hCount : i.groups.length ≤ 3 := by rcases i.groups_count with hc | hc <;> omega
  unfold realEmissionScalarWork
  dsimp only
  split
  · have h := (RealTerminalPacking.prepare i).prepareOutput.emitScalarWork_bound
    omega
  · have h := (RealTerminalPacking.prepare i).prepareOutput.emitMixedScalarWork_bound
    omega

noncomputable def realEmissionArithmeticWork {n : ℕ} (i : TerminalLotto n) : ℕ :=
  let output := (RealTerminalPacking.prepare i).prepareOutput
  match i.realPivot with
  | none => output.emitArithmeticWork
  | some _ => output.emitMixedArithmeticWork

theorem realEmissionArithmeticWork_bound {n : ℕ} (i : TerminalLotto n) :
    i.realEmissionArithmeticWork ≤ 2 * n := by
  unfold realEmissionArithmeticWork
  dsimp only
  split
  · have h := (RealTerminalPacking.prepare i).prepareOutput.emitArithmeticWork_bound
    omega
  · exact (RealTerminalPacking.prepare i).prepareOutput.emitMixedArithmeticWork_bound

end Blotto.TerminalLotto
