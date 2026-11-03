import Blotto.RationalFourParametersCode

/-! The eight scalar programs are evaluated into one native table. Numerical
factories read that table; all mathematical proof fields are erased data. -/

namespace Blotto
open scoped BigOperators

structure RationalFourParameterTable (i : RationalFourInput) where
  table : FixedArrayTable 8 ℚ
  correct : ∀ j, table.read j = RationalFourParametersCode.values i j

namespace RationalFourParameterTable

def prepare (i : RationalFourInput) : RationalFourParameterTable i :=
  let env := RationalFourParametersCode.environment i
  { table := FixedArrayTable.ofFn fun j => (RationalFourParametersCode.programs j).value env
    correct := by intro j; rw [FixedArrayTable.read_ofFn]; exact RationalFourParametersCode.value_eq i j }

def S {i : RationalFourInput} (p : RationalFourParameterTable i) : ℚ := p.table.read 0
@[simp] theorem S_eq {i : RationalFourInput} (p : RationalFourParameterTable i) : p.S = i.S := by
  simpa [S, RationalFourParametersCode.values] using p.correct 0

def auxLength {i : RationalFourInput} (p : RationalFourParameterTable i) : ℚ := p.table.read 1
@[simp] theorem auxLength_eq {i : RationalFourInput} (p : RationalFourParameterTable i) : p.auxLength = i.auxLength := by
  simpa [auxLength, RationalFourParametersCode.values] using p.correct 1

def firstBudget {i : RationalFourInput} (p : RationalFourParameterTable i) : ℚ := p.table.read 2
@[simp] theorem firstBudget_eq {i : RationalFourInput} (p : RationalFourParameterTable i) : p.firstBudget = i.firstBudget := by
  simpa [firstBudget, RationalFourParametersCode.values] using p.correct 2

def secondBudget {i : RationalFourInput} (p : RationalFourParameterTable i) : ℚ := p.table.read 3
@[simp] theorem secondBudget_eq {i : RationalFourInput} (p : RationalFourParameterTable i) : p.secondBudget = i.secondBudget := by
  simpa [secondBudget, RationalFourParametersCode.values] using p.correct 3

def shortFraction {i : RationalFourInput} (p : RationalFourParameterTable i) : ℚ := p.table.read 4
@[simp] theorem shortFraction_eq {i : RationalFourInput} (p : RationalFourParameterTable i) : p.shortFraction = i.shortFraction := by
  simpa [shortFraction, RationalFourParametersCode.values] using p.correct 4

def scaleFraction {i : RationalFourInput} (p : RationalFourParameterTable i) : ℚ := p.table.read 5
@[simp] theorem scaleFraction_eq {i : RationalFourInput} (p : RationalFourParameterTable i) : p.scaleFraction = i.scaleFraction := by
  simpa [scaleFraction, RationalFourParametersCode.values] using p.correct 5

def nestedProbability {i : RationalFourInput} (p : RationalFourParameterTable i) : ℚ := p.table.read 6
@[simp] theorem nestedProbability_eq {i : RationalFourInput} (p : RationalFourParameterTable i) : p.nestedProbability = i.nestedProbability := by
  simpa [nestedProbability, RationalFourParametersCode.values] using p.correct 6

def reflectedBudget {i : RationalFourInput} (p : RationalFourParameterTable i) : ℚ := p.table.read 7
@[simp] theorem reflectedBudget_eq {i : RationalFourInput} (p : RationalFourParameterTable i) : p.reflectedBudget = i.reflectedBudget := by
  simpa [reflectedBudget, RationalFourParametersCode.values] using p.correct 7

def work (i : RationalFourInput) : ℕ :=
  ∑ j : Fin 8, ((RationalFourParametersCode.programs j).run (RationalFourParametersCode.environment i)).2

theorem work_bound (i : RationalFourInput) : work i ≤ 2048 := by
  calc
    _ ≤ ∑ _j : Fin 8, 256 := Finset.sum_le_sum (fun j _ => RationalFourParametersCode.operations i j)
    _ = _ := by simp

end RationalFourParameterTable
end Blotto
