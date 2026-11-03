import Blotto.RealFourParametersCode

/-! The eight scalar programs are evaluated into one native table. Numerical
factories read that table; all mathematical proof fields are erased data. -/

namespace Blotto

structure RealFourParameterTable (i : FourInput) where
  table : FixedArrayTable 8 ℝ
  correct : ∀ j, table.read j = RealFourParametersCode.values i j

namespace RealFourParameterTable

noncomputable def prepare (i : FourInput) : RealFourParameterTable i :=
  let env := RealFourParametersCode.environment i
  { table := FixedArrayTable.ofFn fun j => (RationalFourParametersCode.programs j).realValue env
    correct := by intro j; rw [FixedArrayTable.read_ofFn]; exact RealFourParametersCode.value_eq i j }

noncomputable def S {i : FourInput} (p : RealFourParameterTable i) : ℝ := p.table.read 0
@[simp] theorem S_eq {i : FourInput} (p : RealFourParameterTable i) : p.S = i.S := by
  simpa [S, RealFourParametersCode.values] using p.correct 0

noncomputable def auxLength {i : FourInput} (p : RealFourParameterTable i) : ℝ := p.table.read 1
@[simp] theorem auxLength_eq {i : FourInput} (p : RealFourParameterTable i) : p.auxLength = i.auxLength := by
  simpa [auxLength, RealFourParametersCode.values] using p.correct 1

noncomputable def firstBudget {i : FourInput} (p : RealFourParameterTable i) : ℝ := p.table.read 2
@[simp] theorem firstBudget_eq {i : FourInput} (p : RealFourParameterTable i) : p.firstBudget = i.firstBudget := by
  simpa [firstBudget, RealFourParametersCode.values] using p.correct 2

noncomputable def secondBudget {i : FourInput} (p : RealFourParameterTable i) : ℝ := p.table.read 3
@[simp] theorem secondBudget_eq {i : FourInput} (p : RealFourParameterTable i) : p.secondBudget = i.secondBudget := by
  simpa [secondBudget, RealFourParametersCode.values] using p.correct 3

noncomputable def shortFraction {i : FourInput} (p : RealFourParameterTable i) : ℝ := p.table.read 4
@[simp] theorem shortFraction_eq {i : FourInput} (p : RealFourParameterTable i) : p.shortFraction = i.shortFraction := by
  simpa [shortFraction, RealFourParametersCode.values] using p.correct 4

noncomputable def scaleFraction {i : FourInput} (p : RealFourParameterTable i) : ℝ := p.table.read 5
@[simp] theorem scaleFraction_eq {i : FourInput} (p : RealFourParameterTable i) : p.scaleFraction = i.scaleFraction := by
  simpa [scaleFraction, RealFourParametersCode.values] using p.correct 5

noncomputable def nestedProbability {i : FourInput} (p : RealFourParameterTable i) : ℝ := p.table.read 6
@[simp] theorem nestedProbability_eq {i : FourInput} (p : RealFourParameterTable i) : p.nestedProbability = i.nestedProbability := by
  simpa [nestedProbability, RealFourParametersCode.values] using p.correct 6

noncomputable def reflectedBudget {i : FourInput} (p : RealFourParameterTable i) : ℝ := p.table.read 7
@[simp] theorem reflectedBudget_eq {i : FourInput} (p : RealFourParameterTable i) : p.reflectedBudget = i.reflectedBudget := by
  simpa [reflectedBudget, RealFourParametersCode.values] using p.correct 7

end RealFourParameterTable
end Blotto
