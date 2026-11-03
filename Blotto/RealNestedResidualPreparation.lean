import Blotto.RationalNestedResidualPreparation
import Blotto.RealNestedResidualCompiler
import Blotto.RealNestedParametersCode

/-! The same five residual-field programs have exact-real semantics. One
input/descriptor materialization has unit-price formula/access/write labels;
caller repetition, environment setup, addressing/backend/ownership are separate. -/

namespace Blotto.RealNestedResidualPreparationCode
open RationalNestedResidualPreparationCode
open scoped BigOperators

theorem field_value (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (j : Fin 5) :
    (programs j).realValue (RealNestedParametersCode.environment i 0) =
      (RealNestedResidualCode.environment (i.residualInput hvt htu)).read j := by
  fin_cases j <;> simp [programs, RealNestedResidualCode.environment, FixedArrayTable.read_ofFn,
    NestedInput.residualInput, NestedInput.geometry]

noncomputable def fieldWork (i : NestedInput) : ℕ :=
  ∑ j : Fin 5, (((programs j).runReal (RealNestedParametersCode.environment i 0)).2 + 1)

theorem fieldWork_bound (i : NestedInput) : fieldWork i ≤ 85 := by
  have h : ∀ j : Fin 5, ((programs j).runReal (RealNestedParametersCode.environment i 0)).2 + 1 ≤ 17 := by
    intro j
    have hc := ((programs j).runReal_operations_le (RealNestedParametersCode.environment i 0)).trans (operations j)
    omega
  calc
    _ ≤ ∑ _j : Fin 5, 17 := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

end Blotto.RealNestedResidualPreparationCode
namespace Blotto.NestedInput

noncomputable def realResidualPreparedWork (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) : ℕ :=
  RealNestedResidualPreparationCode.fieldWork i + RealNestedResidualCode.descriptorWork (i.residualInput hvt htu) + 21

theorem realResidualPreparedWork_bound (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) :
    i.realResidualPreparedWork hvt htu ≤ 778 := by
  have hf := RealNestedResidualPreparationCode.fieldWork_bound i
  have hd := RealNestedResidualCode.descriptorWork_bound (i.residualInput hvt htu)
  unfold realResidualPreparedWork
  omega

noncomputable def realPaddedResidualPreparedWork (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) : ℕ :=
  i.realResidualPreparedWork hvt htu + 63

theorem realPaddedResidualPreparedWork_bound (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) :
    i.realPaddedResidualPreparedWork hvt htu ≤ 841 := by
  have h := i.realResidualPreparedWork_bound hvt htu
  unfold realPaddedResidualPreparedWork
  omega

end Blotto.NestedInput
