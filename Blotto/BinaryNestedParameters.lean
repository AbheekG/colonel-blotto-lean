import Blotto.BinarySegmentAssembly
import Blotto.RationalNestedParametersCode

/-! Six stored Boolean nested-input fields evaluate the original location,
conditional/family probabilities, regime coefficients and first geometry.
The retained rational input conditions are proof data; no runtime Rat encoding
or supplied parameter factory is used. -/

namespace Blotto.BinaryNestedParameters
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler

structure Input where
  M : SignedWord
  a : SignedWord
  d : SignedWord
  c : SignedWord
  t : SignedWord
  q : SignedWord

def Input.Canonical (input : Input) : Prop := CanonicalWord input.M ∧ CanonicalWord input.a ∧
  CanonicalWord input.d ∧ CanonicalWord input.c ∧ CanonicalWord input.t ∧ CanonicalWord input.q

def Input.Refines (input : Input) (source : RationalNestedInput) : Prop := value input.M = source.M ∧
  value input.a = source.a ∧ value input.d = source.d ∧ value input.c = source.c ∧
  value input.t = source.t ∧ value input.q = source.q

def environment (input : Input) (x : SignedWord) : FixedArrayTable 7 SignedWord :=
  FixedArrayTable.ofFn ![input.M,input.a,input.d,input.c,input.t,input.q,x]

abbrev Expr := Syntax 7
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
def conditional : Expr := .div (.sub (.sub C H) (.mul (.literal .two) X)) (.sub C X)
def familyProbability : Expr := .div H (.sub C X)
def mirror : Expr := .sub (.add U V) T
def secondAlpha : Expr := .div (.mul mirror (.add H T)) (.mul T (.sub C T))
def thirdAlpha : Expr := .div (.mul V (.add H T)) (.mul T (.add H V))

def firstParameters : Fin 4 → Expr := ![.sub U X, .sub V X, .sub M C, .add H X]


def programs : Fin 9 → Expr := ![H,U,V,location,conditional,familyProbability,mirror,secondAlpha,thirdAlpha]
def sourcePrograms : Fin 9 → RationalExpression 7 := ![RationalNestedParametersCode.H,
  RationalNestedParametersCode.U,RationalNestedParametersCode.V,RationalNestedParametersCode.location,
  RationalNestedParametersCode.conditional,RationalNestedParametersCode.familyProbability,
  RationalNestedParametersCode.mirror,RationalNestedParametersCode.secondAlpha,RationalNestedParametersCode.thirdAlpha]

theorem programs_source (j : Fin 9) : (programs j).rational = sourcePrograms j := by fin_cases j <;> rfl

theorem firstParameters_source (j : Fin 4) : (firstParameters j).rational = RationalNestedParametersCode.firstParameters j := by
  fin_cases j <;> rfl

theorem environment_canonical (input : Input) (x : SignedWord) (h : input.Canonical) (hx : CanonicalWord x) :
    ∀ j, CanonicalWord ((environment input x).read j) := by
  intro j
  simp only [environment,FixedArrayTable.read_ofFn]
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2
  · exact hx

theorem environment_refines (input : Input) (x : SignedWord) (source : RationalNestedInput) (h : input.Refines source) :
    BinaryRationalExpression.interpretedEnvironment (environment input x) = RationalNestedParametersCode.environment source (value x) := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [BinaryRationalExpression.interpretedEnvironment,environment,RationalNestedParametersCode.environment,FixedArrayTable.read_ofFn]
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2
  · rfl

def prepare (input : Input) (x : SignedWord) : FixedArrayTable 9 SignedWord :=
  FixedArrayTable.ofFn (fun j => ((programs j).compile.run (environment input x)).1)

def geometry (input : Input) (x : SignedWord) : FixedArrayTable 4 SignedWord :=
  FixedArrayTable.ofFn (fun j => ((firstParameters j).compile.run (environment input x)).1)

def values (source : RationalNestedInput) (x : ℚ) : Fin 9 → ℚ :=
  ![source.h,source.u,source.v,source.location x,source.conditionalProbability x,
    source.familyProbability x,source.mirrorLength,source.secondAlpha,source.thirdAlpha]

theorem prepare_canonical (input : Input) (x : SignedWord) (h : input.Canonical) (hx : CanonicalWord x) :
    ∀ j, CanonicalWord ((prepare input x).read j) := by
  intro j
  simp only [prepare,FixedArrayTable.read_ofFn]
  exact (programs j).compile.run_canonical _ (environment_canonical input x h hx) (programs j).compile_canonical

theorem prepare_value (input : Input) (x : SignedWord) (source : RationalNestedInput)
    (h : input.Canonical) (hx : CanonicalWord x) (hr : input.Refines source) (j : Fin 9) :
    value ((prepare input x).read j) = values source (value x) j := by
  simp only [prepare,FixedArrayTable.read_ofFn]
  have he := (programs j).compile_run_value (environment input x) (fun r => (environment_canonical input x h hx r).1)
  rw [programs_source,environment_refines input x source hr] at he
  apply he.trans
  change (sourcePrograms j).value (RationalNestedParametersCode.environment source (value x)) = _
  fin_cases j <;> simp [sourcePrograms,values]

theorem geometry_canonical (input : Input) (x : SignedWord) (h : input.Canonical) (hx : CanonicalWord x) :
    ∀ j, CanonicalWord ((geometry input x).read j) := by
  intro j
  simp only [geometry,FixedArrayTable.read_ofFn]
  exact (firstParameters j).compile.run_canonical _ (environment_canonical input x h hx) (firstParameters j).compile_canonical

theorem geometry_refines (input : Input) (x : SignedWord) (source : RationalNestedInput)
    (h : input.Canonical) (hx : CanonicalWord x) (hr : input.Refines source) (htv : source.t ≤ source.v)
    (hs : 0 ≤ value x ∧ value x ≤ source.t) (hp : 0 < source.conditionalProbability (value x)) :
    BinaryRationalExpression.interpretedEnvironment (geometry input x) =
      RationalThreeGeometryCode.environment (source.firstGeometry htv (value x) hs hp) := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [BinaryRationalExpression.interpretedEnvironment,geometry,FixedArrayTable.read_ofFn]
  have he := (firstParameters j).compile_run_value (environment input x) (fun r => (environment_canonical input x h hx r).1)
  rw [firstParameters_source,environment_refines input x source hr] at he
  exact he.trans (RationalNestedParametersCode.firstParameters_value source htv (value x) hs hp j)

end Blotto.BinaryNestedParameters
