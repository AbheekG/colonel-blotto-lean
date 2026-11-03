import Blotto.RationalSecondUniformPreparation
import Blotto.RealThreeInputPreparation
import Blotto.RealNestedParametersCode

/-! Exact-real translated-uniform construction uses the same numerical field
programs. Formula/access/write labels include mirror evaluation and a complete
translated descriptor. Invocation counts and physical storage stay separate. -/

namespace Blotto.RealSecondUniformPreparationCode
open RationalSecondUniformCode
open scoped BigOperators

theorem field_value (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) (j : Fin 5) :
    (programs j).realValue (RealNestedParametersCode.environment i 0) =
      (RealThreeInputPreparationCode.environment (i.secondUniformInput htu hTt)).read j := by
  fin_cases j <;> simp [programs, RealThreeInputPreparationCode.environment, FixedArrayTable.read_ofFn,
    NestedInput.secondUniformInput]

noncomputable def fieldWork (i : NestedInput) : ℕ :=
  ∑ j : Fin 5, (((programs j).runReal (RealNestedParametersCode.environment i 0)).2 + 1)

theorem fieldWork_bound (i : NestedInput) : fieldWork i ≤ 645 := by
  have h : ∀ j : Fin 5, ((programs j).runReal (RealNestedParametersCode.environment i 0)).2 + 1 ≤ 129 := by
    intro j
    have hp := ((programs j).runReal_operations_le (RealNestedParametersCode.environment i 0)).trans (operations j)
    omega
  calc
    _ ≤ ∑ _j : Fin 5, 129 := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

noncomputable def mirrorWork (i : NestedInput) : ℕ :=
  ((RationalNestedParametersCode.scalarPrograms 3).runReal (RealNestedParametersCode.environment i 0)).2 + 1

theorem mirrorWork_bound (i : NestedInput) : mirrorWork i ≤ 129 := by
  have h := RealNestedParametersCode.scalar_operations i 0 3
  unfold mirrorWork
  omega

end Blotto.RealSecondUniformPreparationCode
namespace Blotto.NestedInput

noncomputable def realSecondUniformPreparedWork (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) : ℕ :=
  RealSecondUniformPreparationCode.mirrorWork i + RealSecondUniformPreparationCode.fieldWork i +
    RealThreeInputPreparationCode.preparedInputWork (i.secondUniformInput htu hTt) + 117

theorem realSecondUniformPreparedWork_bound (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) :
    i.realSecondUniformPreparedWork htu hTt ≤ 3734 := by
  have hm := RealSecondUniformPreparationCode.mirrorWork_bound i
  have hf := RealSecondUniformPreparationCode.fieldWork_bound i
  have ht := RealThreeInputPreparationCode.preparedInputWork_bound (i.secondUniformInput htu hTt)
  unfold realSecondUniformPreparedWork
  omega

end Blotto.NestedInput
