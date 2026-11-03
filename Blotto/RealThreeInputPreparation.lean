import Blotto.RationalThreeInputPreparation
import Blotto.RealThreeInputCompiler

/-! The ordered three-input regime and geometry fields have counted exact-real
semantics. One descriptor materialization prices formula/access/write labels;
environment setup, caller repetition and physical storage are separate. -/

namespace Blotto.RealThreeInputPreparationCode
open RationalThreeInputCode
open scoped BigOperators

noncomputable def environment (i : ThreeInput) : FixedArrayTable 5 ℝ := FixedArrayTable.ofFn ![i.B, i.a, i.d, i.c, i.p]

theorem regime_value (i : ThreeInput) : regime.realValue (environment i) = i.a + i.d - i.B := by
  simp [regime, A, D, B, environment, FixedArrayTable.read_ofFn]

theorem parameter_value (i : ThreeInput) (hE : 0 < i.a + i.d - i.B) (j : Fin 4) :
    (parameters j).realValue (environment i) = (RealThreeGeometryCode.environment (i.geometry hE)).read j := by
  fin_cases j <;> simp [parameters, B, A, D, C, P, environment, FixedArrayTable.read_ofFn,
    RealThreeGeometryCode.environment, ThreeInput.geometry]

noncomputable def regimeWork (i : ThreeInput) : ℕ := (regime.runReal (environment i)).2 + 3

theorem regimeWork_bound (i : ThreeInput) : regimeWork i ≤ 8 := by
  have h := regime.runReal_operations_le (environment i)
  have ho : regime.operationBound = 5 := by decide
  rw [ho] at h
  unfold regimeWork
  omega

noncomputable def fieldWork (i : ThreeInput) : ℕ :=
  ∑ j : Fin 4, (((parameters j).runReal (environment i)).2 + 1)

theorem fieldWork_bound (i : ThreeInput) : fieldWork i ≤ 36 := by
  have h : ∀ j : Fin 4, ((parameters j).runReal (environment i)).2 + 1 ≤ 9 := by
    intro j
    have hp := ((parameters j).runReal_operations_le (environment i)).trans (parameter_operations j)
    omega
  calc
    _ ≤ ∑ _j : Fin 4, 9 := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

noncomputable def preparedInputWork (i : ThreeInput) : ℕ :=
  regimeWork i + if hE : 0 < i.a + i.d - i.B then
    fieldWork i + RealThreeGeometryCode.descriptorWork (i.geometry hE) + 63
  else 63

theorem preparedInputWork_bound (i : ThreeInput) : preparedInputWork i ≤ 2843 := by
  have hGuard := regimeWork_bound i
  have hFields := fieldWork_bound i
  unfold preparedInputWork
  split
  · rename_i hE
    have hDesc := RealThreeGeometryCode.descriptorWork_bound (i.geometry hE)
    omega
  · omega

end Blotto.RealThreeInputPreparationCode
