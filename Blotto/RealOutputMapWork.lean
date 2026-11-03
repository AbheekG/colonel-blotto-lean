import Blotto.RationalReflectionOutputCost
import Blotto.RationalFourPermutationCost
import Blotto.RealExpression

/-! The counted dense output rows also have exact-real semantics. Unit-price
expression/access and result-write labels bound reflection/permutation. Input
production, indices, physical storage and IEEE execution are separate. -/

namespace Blotto.RealReflectionOutputCode
open scoped BigOperators

noncomputable def environment (length x : Allocation 3) (j : Fin 4) : FixedArrayTable 4 ℝ :=
  FixedArrayTable.ofFn ![x 0, x 1, x 2, ![length 0, length 1, length 2, 0] j]

theorem row_value (length x : Allocation 3) (j : Fin 4) :
    (RationalReflectionCode.row j).realValue (environment length x j) = Blotto.reflectAppend length x j := by
  fin_cases j <;> simp [RationalReflectionCode.row, environment, FixedArrayTable.read_ofFn, Blotto.reflectAppend] <;> ring

noncomputable def outputWork (length x : Allocation 3) : ℕ :=
  ∑ j : Fin 4, (((RationalReflectionCode.row j).runReal (environment length x j)).2 + 1)

theorem outputWork_bound (length x : Allocation 3) : outputWork length x ≤ 64 := by
  have h : ∀ j : Fin 4, ((RationalReflectionCode.row j).runReal (environment length x j)).2 + 1 ≤ 16 := by
    intro j
    have hp := ((RationalReflectionCode.row j).runReal_operations_le (environment length x j)).trans
      (RationalReflectionCode.row_operations j)
    omega
  calc
    _ ≤ ∑ _j : Fin 4, 16 := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

end Blotto.RealReflectionOutputCode
namespace Blotto.RealFourPermutationOutputCode
open scoped BigOperators

noncomputable def environment (x : Allocation 4) : FixedArrayTable 4 ℝ := FixedArrayTable.ofFn x

theorem row_value (k : Fin 4) (x : Allocation 4) :
    (RationalFourPermutationCode.row k).realValue (environment x) = x k := by
  fin_cases k <;> simp [RationalFourPermutationCode.row, environment, FixedArrayTable.read_ofFn]

theorem row_permutation_value (π : Equiv.Perm (Fin 4)) (x : Allocation 4) (j : Fin 4) :
    (RationalFourPermutationCode.row (π j)).realValue (environment x) = permuteAllocation π x j := by
  rw [row_value]
  rfl

noncomputable def outputWork (π : Equiv.Perm (Fin 4)) (x : Allocation 4) : ℕ :=
  ∑ j : Fin 4, (((RationalFourPermutationCode.row (π j)).runReal (environment x)).2 + 1)

theorem outputWork_bound (π : Equiv.Perm (Fin 4)) (x : Allocation 4) : outputWork π x ≤ 80 := by
  have h : ∀ j : Fin 4, ((RationalFourPermutationCode.row (π j)).runReal (environment x)).2 + 1 ≤ 20 := by
    intro j
    have hp := ((RationalFourPermutationCode.row (π j)).runReal_operations_le (environment x)).trans
      (RationalFourPermutationCode.row_operations (π j))
    omega
  calc
    _ ≤ ∑ _j : Fin 4, 20 := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

end Blotto.RealFourPermutationOutputCode
