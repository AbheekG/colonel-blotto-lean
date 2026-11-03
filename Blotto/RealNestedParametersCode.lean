import Blotto.RealExpression
import Blotto.RationalNestedParametersBounds
import Blotto.RealThreeGeometryCode
import Blotto.NestedSecond
import Blotto.NestedThird

/-! Counted real evaluation of all nested scalar parameters and the first
conditional geometry transform. Their scopes are the retained NestedInput's. -/

namespace Blotto.RealNestedParametersCode
open RationalNestedParametersCode
open scoped BigOperators

noncomputable def environment (i : NestedInput) (x : ℝ) : FixedArrayTable 7 ℝ :=
  FixedArrayTable.ofFn ![i.M, i.a, i.d, i.c, i.t, i.q, x]

@[simp] theorem M_value (i : NestedInput) (x : ℝ) : M.realValue (environment i x) = i.M := by simp [M, environment, FixedArrayTable.read_ofFn]
@[simp] theorem A_value (i : NestedInput) (x : ℝ) : A.realValue (environment i x) = i.a := by simp [A, environment, FixedArrayTable.read_ofFn]
@[simp] theorem D_value (i : NestedInput) (x : ℝ) : D.realValue (environment i x) = i.d := by simp [D, environment, FixedArrayTable.read_ofFn]
@[simp] theorem C_value (i : NestedInput) (x : ℝ) : C.realValue (environment i x) = i.c := by simp [C, environment, FixedArrayTable.read_ofFn]
@[simp] theorem T_value (i : NestedInput) (x : ℝ) : T.realValue (environment i x) = i.t := by simp [T, environment, FixedArrayTable.read_ofFn]
@[simp] theorem Q_value (i : NestedInput) (x : ℝ) : Q.realValue (environment i x) = i.q := by simp [Q, environment, FixedArrayTable.read_ofFn]
@[simp] theorem X_value (i : NestedInput) (x : ℝ) : X.realValue (environment i x) = x := by simp [X, environment, FixedArrayTable.read_ofFn]
@[simp] theorem H_value (i : NestedInput) (x : ℝ) : H.realValue (environment i x) = i.h := by simp [H, NestedInput.h]
@[simp] theorem U_value (i : NestedInput) (x : ℝ) : U.realValue (environment i x) = i.u := by simp [U, NestedInput.u]
@[simp] theorem V_value (i : NestedInput) (x : ℝ) : V.realValue (environment i x) = i.v := by simp [V, NestedInput.v]

@[simp] theorem location_value (i : NestedInput) (x : ℝ) : location.realValue (environment i x) = i.location x := by simp [location, NestedInput.location]
@[simp] theorem conditional_value (i : NestedInput) (x : ℝ) : conditional.realValue (environment i x) = i.conditionalProbability x := by simp [conditional, NestedInput.conditionalProbability]
@[simp] theorem familyProbability_value (i : NestedInput) (x : ℝ) : familyProbability.realValue (environment i x) = i.familyProbability x := by simp [familyProbability, NestedInput.familyProbability]
@[simp] theorem mirror_value (i : NestedInput) (x : ℝ) : mirror.realValue (environment i x) = i.mirrorLength := by simp [mirror, NestedInput.mirrorLength]
@[simp] theorem secondAlpha_value (i : NestedInput) (x : ℝ) : secondAlpha.realValue (environment i x) = i.secondAlpha := by simp [secondAlpha, NestedInput.secondAlpha]
@[simp] theorem thirdAlpha_value (i : NestedInput) (x : ℝ) : thirdAlpha.realValue (environment i x) = i.thirdAlpha := by simp [thirdAlpha, NestedInput.thirdAlpha]

noncomputable def scalarValues (i : NestedInput) (x : ℝ) : Fin 6 → ℝ :=
  ![i.location x, i.conditionalProbability x, i.familyProbability x, i.mirrorLength, i.secondAlpha, i.thirdAlpha]

theorem scalar_value (i : NestedInput) (x : ℝ) (j : Fin 6) :
    (scalarPrograms j).realValue (environment i x) = scalarValues i x j := by
  fin_cases j <;> simp [scalarPrograms, scalarValues]

theorem firstParameters_value (i : NestedInput) (htv : i.t ≤ i.v) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ i.t) (hp : 0 < i.conditionalProbability x) (j : Fin 4) :
    (firstParameters j).realValue (environment i x) =
      (RealThreeGeometryCode.environment (i.firstGeometry htv x hx hp)).read j := by
  fin_cases j <;> simp [firstParameters, NestedInput.firstGeometry, RealThreeGeometryCode.environment, FixedArrayTable.read_ofFn]

theorem scalar_operations (i : NestedInput) (x : ℝ) (j : Fin 6) :
    ((scalarPrograms j).runReal (environment i x)).2 ≤ 128 :=
  ((scalarPrograms j).runReal_operations_le _).trans (scalar_operationBound j)

theorem firstParameters_operations (i : NestedInput) (x : ℝ) (j : Fin 4) :
    ((firstParameters j).runReal (environment i x)).2 ≤ 16 :=
  ((firstParameters j).runReal_operations_le _).trans (first_parameter_operationBound j)

noncomputable def scalarWork (i : NestedInput) (x : ℝ) : ℕ :=
  ∑ j : Fin 6, ((scalarPrograms j).runReal (environment i x)).2

theorem scalarWork_bound (i : NestedInput) (x : ℝ) : scalarWork i x ≤ 768 := by
  calc
    _ ≤ ∑ _j : Fin 6, 128 := Finset.sum_le_sum (fun j _ => scalar_operations i x j)
    _ = _ := by simp

noncomputable def firstParametersWork (i : NestedInput) (x : ℝ) : ℕ :=
  ∑ j : Fin 4, ((firstParameters j).runReal (environment i x)).2

theorem firstParametersWork_bound (i : NestedInput) (x : ℝ) : firstParametersWork i x ≤ 64 := by
  calc
    _ ≤ ∑ _j : Fin 4, 16 := Finset.sum_le_sum (fun j _ => firstParameters_operations i x j)
    _ = _ := by simp

end Blotto.RealNestedParametersCode
