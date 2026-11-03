import Blotto.RealExpression
import Blotto.RationalFourParametersCode
import Blotto.FourSmallParameters

/-! Real evaluation of the same eight counted four-variable scalar programs.
The exact original parameter formulas and promise boundaries are retained. -/

namespace Blotto.RealFourParametersCode
open RationalFourParametersCode
open scoped BigOperators

noncomputable def values (i : FourInput) : Fin 8 → ℝ :=
  ![i.S, i.auxLength, i.firstBudget, i.secondBudget, i.shortFraction, i.scaleFraction,
    i.nestedProbability, i.reflectedBudget]
noncomputable def environment (i : FourInput) : FixedArrayTable 6 ℝ :=
  FixedArrayTable.ofFn ![i.B, i.u, i.v, i.w, i.ell, i.p]

theorem value_eq (i : FourInput) (j : Fin 8) :
    (programs j).realValue (environment i) = values i j := by
  fin_cases j <;> simp [programs, values, S, auxiliary, firstBudget, secondBudget, shortFraction,
    scaleFraction, nestedProbability, reflectedBudget, U, V, W, L, P, environment,
    FixedArrayTable.read_ofFn, FourInput.S, FourInput.auxLength, FourInput.firstBudget,
    FourInput.secondBudget, FourInput.shortFraction, FourInput.scaleFraction,
    FourInput.nestedProbability, FourInput.reflectedBudget]

theorem operations (i : FourInput) (j : Fin 8) :
    ((programs j).runReal (environment i)).2 ≤ 256 :=
  ((programs j).runReal_operations_le _).trans (operationBound j)

noncomputable def work (i : FourInput) : ℕ := ∑ j : Fin 8, ((programs j).runReal (environment i)).2

theorem work_bound (i : FourInput) : work i ≤ 2048 := by
  calc
    _ ≤ ∑ _j : Fin 8, 256 := Finset.sum_le_sum (fun j _ => operations i j)
    _ = _ := by simp

end Blotto.RealFourParametersCode
