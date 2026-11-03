import Blotto.RationalExpressionValue
import Blotto.RationalExpressionLiteralHeight
import Blotto.RationalNestedParameters

/-! Counted arithmetic code for the actual interior nested parameters,
location, conditional probability, and second/third mixture coefficients. -/

namespace Blotto.RationalNestedParametersCode

abbrev Expr := RationalExpression 7

def M : Expr := .input 0
def A : Expr := .input 1
def D : Expr := .input 2
def C : Expr := .input 3
def T : Expr := .input 4
def Q : Expr := .input 5
def X : Expr := .input 6

def H : Expr := .mul Q (.sub C T)
def U : Expr := .sub M A
def V : Expr := .sub M D

def location : Expr := .div (.mul (.mul H T) X) (.sub (.add H T) (.mul T X))
def conditional : Expr := .div (.sub (.sub C H) (.mul (.literal 2) X)) (.sub C X)
def familyProbability : Expr := .div H (.sub C X)
def mirror : Expr := .sub (.add U V) T
def secondAlpha : Expr := .div (.mul mirror (.add H T)) (.mul T (.sub C T))
def thirdAlpha : Expr := .div (.mul V (.add H T)) (.mul T (.add H V))

def firstParameters : Fin 4 → Expr := ![.sub U X, .sub V X, .sub M C, .add H X]

def environment (i : RationalNestedInput) (x : ℚ) : FixedArrayTable 7 ℚ :=
  FixedArrayTable.ofFn ![i.M, i.a, i.d, i.c, i.t, i.q, x]

@[simp] theorem M_value (i : RationalNestedInput) (x : ℚ) : M.value (environment i x) = i.M := by simp [M, environment, FixedArrayTable.read_ofFn]
@[simp] theorem A_value (i : RationalNestedInput) (x : ℚ) : A.value (environment i x) = i.a := by simp [A, environment, FixedArrayTable.read_ofFn]
@[simp] theorem D_value (i : RationalNestedInput) (x : ℚ) : D.value (environment i x) = i.d := by simp [D, environment, FixedArrayTable.read_ofFn]
@[simp] theorem C_value (i : RationalNestedInput) (x : ℚ) : C.value (environment i x) = i.c := by simp [C, environment, FixedArrayTable.read_ofFn]
@[simp] theorem T_value (i : RationalNestedInput) (x : ℚ) : T.value (environment i x) = i.t := by simp [T, environment, FixedArrayTable.read_ofFn]
@[simp] theorem Q_value (i : RationalNestedInput) (x : ℚ) : Q.value (environment i x) = i.q := by simp [Q, environment, FixedArrayTable.read_ofFn]
@[simp] theorem X_value (i : RationalNestedInput) (x : ℚ) : X.value (environment i x) = x := by simp [X, environment, FixedArrayTable.read_ofFn]
@[simp] theorem H_value (i : RationalNestedInput) (x : ℚ) : H.value (environment i x) = i.h := by simp [H, RationalNestedInput.h]
@[simp] theorem U_value (i : RationalNestedInput) (x : ℚ) : U.value (environment i x) = i.u := by simp [U, RationalNestedInput.u]
@[simp] theorem V_value (i : RationalNestedInput) (x : ℚ) : V.value (environment i x) = i.v := by simp [V, RationalNestedInput.v]

@[simp] theorem location_value (i : RationalNestedInput) (x : ℚ) : location.value (environment i x) = i.location x := by simp [location, RationalNestedInput.location]
@[simp] theorem conditional_value (i : RationalNestedInput) (x : ℚ) : conditional.value (environment i x) = i.conditionalProbability x := by simp [conditional, RationalNestedInput.conditionalProbability]
@[simp] theorem familyProbability_value (i : RationalNestedInput) (x : ℚ) : familyProbability.value (environment i x) = i.familyProbability x := by simp [familyProbability, RationalNestedInput.familyProbability]
@[simp] theorem mirror_value (i : RationalNestedInput) (x : ℚ) : mirror.value (environment i x) = i.mirrorLength := by simp [mirror, RationalNestedInput.mirrorLength]
@[simp] theorem secondAlpha_value (i : RationalNestedInput) (x : ℚ) : secondAlpha.value (environment i x) = i.secondAlpha := by simp [secondAlpha, RationalNestedInput.secondAlpha]
@[simp] theorem thirdAlpha_value (i : RationalNestedInput) (x : ℚ) : thirdAlpha.value (environment i x) = i.thirdAlpha := by simp [thirdAlpha, RationalNestedInput.thirdAlpha]

theorem firstParameters_value (i : RationalNestedInput) (htv : i.t ≤ i.v) (x : ℚ)
    (hx : 0 ≤ x ∧ x ≤ i.t) (hp : 0 < i.conditionalProbability x) (j : Fin 4) :
    (firstParameters j).value (environment i x) =
      (RationalThreeGeometryCode.environment (i.firstGeometry htv x hx hp)).read j := by
  fin_cases j <;> simp [firstParameters, RationalNestedInput.firstGeometry,
    RationalThreeGeometryCode.environment, FixedArrayTable.read_ofFn]

end Blotto.RationalNestedParametersCode
