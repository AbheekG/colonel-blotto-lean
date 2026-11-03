import Blotto.RationalExpressionValue
import Blotto.RationalThreeGeometry

/-! Counted programs for the actual native three-variable geometric
parameters and vertices, with a four-word stored environment. -/

namespace Blotto.RationalThreeGeometryCode

abbrev Expr := RationalExpression 4

def U : Expr := .input 0
def V : Expr := .input 1
def W : Expr := .input 2
def H : Expr := .input 3

def A : Expr := .add (.add V W) H
def D : Expr := .add (.add U W) H
def C : Expr := .add (.add U V) H
def Budget : Expr := .add (.add (.add U V) W) H
def E : Expr := .add W H
def F : Expr := .add U H
def G : Expr := .add V H
def R : Expr := .add (.add (H.power 2) (.mul H (.add U W))) (.mul W (.add U V))
def S : Expr := .add (.add (.add (.add (H.power 3)
  (.mul (.add (.add U V) W) (H.power 2)))
  (.mul (.add (.add (.mul U V) (.mul U W)) (.mul V W)) H))
  (.mul (.mul U V) W)) (.mul (V.power 2) W)

def environment (g : RationalThreeGeometry) : FixedArrayTable 4 ℚ := FixedArrayTable.ofFn ![g.u, g.v, g.w, g.h]

@[simp] theorem U_value (g : RationalThreeGeometry) : U.value (environment g) = g.u := by simp [U, environment, FixedArrayTable.read_ofFn]
@[simp] theorem V_value (g : RationalThreeGeometry) : V.value (environment g) = g.v := by simp [V, environment, FixedArrayTable.read_ofFn]
@[simp] theorem W_value (g : RationalThreeGeometry) : W.value (environment g) = g.w := by simp [W, environment, FixedArrayTable.read_ofFn]
@[simp] theorem H_value (g : RationalThreeGeometry) : H.value (environment g) = g.h := by simp [H, environment, FixedArrayTable.read_ofFn]

@[simp] theorem A_value (g : RationalThreeGeometry) : A.value (environment g) = g.a := by simp [A, RationalThreeGeometry.a]
@[simp] theorem D_value (g : RationalThreeGeometry) : D.value (environment g) = g.d := by simp [D, RationalThreeGeometry.d]
@[simp] theorem C_value (g : RationalThreeGeometry) : C.value (environment g) = g.c := by simp [C, RationalThreeGeometry.c]
@[simp] theorem Budget_value (g : RationalThreeGeometry) : Budget.value (environment g) = g.budget := by simp [Budget, RationalThreeGeometry.budget]
@[simp] theorem E_value (g : RationalThreeGeometry) : E.value (environment g) = g.E := by simp [E, RationalThreeGeometry.E]
@[simp] theorem F_value (g : RationalThreeGeometry) : F.value (environment g) = g.F := by simp [F, RationalThreeGeometry.F]
@[simp] theorem G_value (g : RationalThreeGeometry) : G.value (environment g) = g.G := by simp [G, RationalThreeGeometry.G]
@[simp] theorem R_value (g : RationalThreeGeometry) : R.value (environment g) = g.R := by simp [R, RationalThreeGeometry.R]
@[simp] theorem S_value (g : RationalThreeGeometry) : S.value (environment g) = g.S := by simp [S, RationalThreeGeometry.S]

def vertex : Fin 6 → Fin 3 → Expr :=
  ![![.literal 0, W, C], ![W, .literal 0, C], ![A, .literal 0, U],
    ![A, U, .literal 0], ![V, D, .literal 0], ![.literal 0, D, V]]

theorem vertex_value (g : RationalThreeGeometry) (i : Fin 6) (j : Fin 3) :
    (vertex i j).value (environment g) = g.vertex i j := by
  fin_cases i <;> fin_cases j <;> simp [vertex, RationalThreeGeometry.vertex]

end Blotto.RationalThreeGeometryCode
