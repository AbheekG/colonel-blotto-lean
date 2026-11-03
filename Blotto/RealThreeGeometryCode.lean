import Blotto.RealExpression
import Blotto.RationalThreeCodeBounds
import Blotto.ThreeLottery

/-! The retained counted three-variable formulas evaluate over real inputs,
including boundary weights and both ordering comparisons. -/

namespace Blotto.RealThreeGeometryCode
open RationalThreeGeometryCode

noncomputable def environment (g : ThreeGeometry) : FixedArrayTable 4 ℝ := FixedArrayTable.ofFn ![g.u, g.v, g.w, g.h]

@[simp] theorem U_value (g : ThreeGeometry) : U.realValue (environment g) = g.u := by simp [U, environment, FixedArrayTable.read_ofFn]
@[simp] theorem V_value (g : ThreeGeometry) : V.realValue (environment g) = g.v := by simp [V, environment, FixedArrayTable.read_ofFn]
@[simp] theorem W_value (g : ThreeGeometry) : W.realValue (environment g) = g.w := by simp [W, environment, FixedArrayTable.read_ofFn]
@[simp] theorem H_value (g : ThreeGeometry) : H.realValue (environment g) = g.h := by simp [H, environment, FixedArrayTable.read_ofFn]

@[simp] theorem A_value (g : ThreeGeometry) : A.realValue (environment g) = g.a := by simp [A, ThreeGeometry.a]
@[simp] theorem D_value (g : ThreeGeometry) : D.realValue (environment g) = g.d := by simp [D, ThreeGeometry.d]
@[simp] theorem C_value (g : ThreeGeometry) : C.realValue (environment g) = g.c := by simp [C, ThreeGeometry.c]
@[simp] theorem Budget_value (g : ThreeGeometry) : Budget.realValue (environment g) = g.budget := by simp [Budget, ThreeGeometry.budget]
@[simp] theorem E_value (g : ThreeGeometry) : E.realValue (environment g) = g.E := by simp [E, ThreeGeometry.E]
@[simp] theorem F_value (g : ThreeGeometry) : F.realValue (environment g) = g.F := by simp [F, ThreeGeometry.F]
@[simp] theorem G_value (g : ThreeGeometry) : G.realValue (environment g) = g.G := by simp [G, ThreeGeometry.G]
@[simp] theorem R_value (g : ThreeGeometry) : R.realValue (environment g) = g.R := by simp [R, ThreeGeometry.R]
@[simp] theorem S_value (g : ThreeGeometry) : S.realValue (environment g) = g.S := by simp [S, ThreeGeometry.S]

theorem vertex_value (g : ThreeGeometry) (i : Fin 6) (j : Fin 3) :
    (vertex i j).realValue (environment g) = g.vertex i j := by
  fin_cases i <;> fin_cases j <;> simp [vertex, ThreeGeometry.vertex]

theorem first_value (g : ThreeGeometry) (slot : Fin 9) :
    (first slot).realValue (environment g) = g.firstWeights.vector slot := by
  fin_cases slot <;> simp [first, ThreeGeometry.firstWeights, SegmentWeights.vector]

theorem second_value (g : ThreeGeometry) (slot : Fin 9) :
    (second slot).realValue (environment g) = g.secondWeights.vector slot := by
  fin_cases slot <;> simp [second, ThreeGeometry.secondWeights, SegmentWeights.vector]

theorem third_value (g : ThreeGeometry) (slot : Fin 9) :
    (third slot).realValue (environment g) = g.thirdWeights.vector slot := by
  fin_cases slot <;> simp [third, ThreeGeometry.thirdWeights, SegmentWeights.vector]

theorem chosen_value (g : ThreeGeometry) (slot : Fin 9) :
    (chosen slot).realValue (environment g) = g.chosenWeights.vector slot := by
  by_cases h1 : g.w ≤ g.v
  · simp [chosen, ThreeGeometry.chosenWeights, h1, first_value]
  · by_cases h2 : g.w ≤ g.u
    · simp [chosen, ThreeGeometry.chosenWeights, h1, h2, second_value]
    · simp [chosen, ThreeGeometry.chosenWeights, h1, h2, third_value]

theorem chosen_operations (g : ThreeGeometry) (slot : Fin 9) : ((chosen slot).runReal (environment g)).2 ≤ 256 :=
  ((chosen slot).runReal_operations_le _).trans (chosen_operationBound slot)

theorem vertex_operations (g : ThreeGeometry) (i : Fin 6) (j : Fin 3) : ((vertex i j).runReal (environment g)).2 ≤ 8 :=
  ((vertex i j).runReal_operations_le _).trans (vertex_operationBound i j)

end Blotto.RealThreeGeometryCode
