import Blotto.BinaryThreeInputCompiler
import Blotto.RationalFourParametersCode

/-! Actual six stored Boolean input words compile all eight retained ordered
four-variable parameters. Explicit small literals realize the original total
divisions/maxima; canonical outputs and source-height work are derived. Input
admissibility remains proof data, not a runtime recognizer. -/

namespace Blotto.BinaryFourParameters
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler
open scoped BigOperators

structure Input where
  B : SignedWord
  u : SignedWord
  v : SignedWord
  w : SignedWord
  ell : SignedWord
  p : SignedWord

def Input.environment (input : Input) : FixedArrayTable 6 SignedWord := FixedArrayTable.ofFn
  ![input.B,input.u,input.v,input.w,input.ell,input.p]
def Input.Canonical (input : Input) : Prop := CanonicalWord input.B ∧ CanonicalWord input.u ∧
  CanonicalWord input.v ∧ CanonicalWord input.w ∧ CanonicalWord input.ell ∧ CanonicalWord input.p
def Input.Refines (input : Input) (source : RationalFourInput) : Prop := value input.B = source.B ∧
  value input.u = source.u ∧ value input.v = source.v ∧ value input.w = source.w ∧
  value input.ell = source.ell ∧ value input.p = source.p

abbrev Expr := Syntax 6
def B : Expr := .input 0
def U : Expr := .input 1
def V : Expr := .input 2
def W : Expr := .input 3
def L : Expr := .input 4
def P : Expr := .input 5
def S : Expr := .add (.add U V) W
def auxiliary : Expr := .maximum (.maximum (.maximum (.sub V U) (.sub W (.mul P L)))
    (.sub (.mul (.sub (.literal .two) P) L) W)) (.literal .zero)
def firstBudget : Expr := .div (.add (.add U V) auxiliary) (.literal .two)
def secondBudget : Expr := .div (.add (.add auxiliary W) (.mul P L)) (.literal .two)
def shortFraction : Expr := .div (.mul (.sub (.literal .one) P) L) S
def scaleFraction : Expr := .sub (.literal .one) shortFraction
def nestedProbability : Expr := .div (.mul P L) (.sub S (.mul (.sub (.literal .one) P) L))
def reflectedBudget : Expr := .div (.sub S (.mul P L)) (.literal .two)
def programs : Fin 8 → Expr := ![S,auxiliary,firstBudget,secondBudget,shortFraction,scaleFraction,nestedProbability,reflectedBudget]

theorem programs_source (j : Fin 8) : (programs j).rational = RationalFourParametersCode.programs j := by fin_cases j <;> rfl
theorem programs_interpreted (j : Fin 8) : (programs j).compile.interpreted = RationalFourParametersCode.programs j :=
  (programs j).compile_interpreted.trans (programs_source j)

theorem input_canonical (input : Input) (h : input.Canonical) : ∀ j, CanonicalWord (input.environment.read j) := by
  intro j
  fin_cases j <;> simp only [Input.environment,FixedArrayTable.read_ofFn]
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2

theorem input_environment (input : Input) (source : RationalFourInput) (h : input.Refines source) :
    BinaryRationalExpression.interpretedEnvironment input.environment = RationalFourParametersCode.environment source := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  rw [BinaryRationalExpression.interpretedEnvironment,FixedArrayTable.read_ofFn]
  unfold Input.environment RationalFourParametersCode.environment
  rw [FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2

def prepare (input : Input) : FixedArrayTable 8 SignedWord :=
  FixedArrayTable.ofFn (fun j => ((programs j).compile.run input.environment).1)

theorem prepare_canonical (input : Input) (h : input.Canonical) : ∀ j, CanonicalWord ((prepare input).read j) := by
  intro j
  rw [prepare,FixedArrayTable.read_ofFn]
  exact (programs j).compile.run_canonical input.environment (input_canonical input h) (programs j).compile_canonical

theorem prepare_value (input : Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (j : Fin 8) :
    value ((prepare input).read j) = RationalFourParametersCode.values source j := by
  rw [prepare,FixedArrayTable.read_ofFn]
  have he := (programs j).compile_run_value input.environment (fun r => (input_canonical input hC r).1)
  rw [programs_source,input_environment input source hR] at he
  exact he.trans (RationalFourParametersCode.value_eq source j)

theorem compiled_sizes (j : Fin 8) : (programs j).compileAllocated ≤ 1536 ∧
    (programs j).compile.syntaxNodes ≤ 256 ∧ (programs j).compile.literalCount ≤ 256 := by fin_cases j <;> decide

def prepareWork (input : Input) : ℕ :=
  2 * BinaryRationalExpression.environmentPayload input.environment +
    (∑ j : Fin 8, (programs j).compile.bitWork input.environment) + 12344
def prepareWithWork (input : Input) : FixedArrayTable 8 SignedWord × ℕ := (prepare input,prepareWork input)

theorem prepareWork_bound (input : Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ j, RationalHeight ((RationalFourParametersCode.environment source).read j) s) :
    prepareWork input ≤ 12 * (4*s+3) + 2048 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 12) + 12344 := by
  have hc := input_canonical input hC
  have hi := input_environment input source hR
  have hh : ∀ j, RationalHeight (value (input.environment.read j)) s := by
    intro j
    have he := hHeight j
    rw [← hi] at he
    simpa only [BinaryRationalExpression.interpretedEnvironment,FixedArrayTable.read_ofFn] using he
  have hp := BinaryRationalExpression.environmentPayload_bound input.environment s hc hh
  have hEach : ∀ j, (programs j).compile.bitWork input.environment ≤ 256 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 12) := by
    intro j
    have he := (programs j).compile.bitWork_bound input.environment hc (programs j).compile_canonical _
      (by rw [programs_interpreted,hi]; exact RationalFourParametersCode.intermediates source j s hs hHeight)
    rw [programs_interpreted] at he
    exact he.trans (Nat.mul_le_mul_right _ (RationalFourParametersCode.operationBound j))
  have hSum : (∑ j : Fin 8, (programs j).compile.bitWork input.environment) ≤
      2048 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 12) :=
    (Finset.sum_le_sum (fun j _ => hEach j)).trans_eq (by simp; ring)
  unfold prepareWork
  omega

def parameterStorageBound (s : ℕ) : ℕ :=
  6 * (4 * expressionHeightBudget s 12 + 3) + 295 * (8 * expressionHeightBudget s 12 + 7) +
    4 * 270 + 256 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 12)

theorem parameter_workspace (input : Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ j, RationalHeight ((RationalFourParametersCode.environment source).read j) s) :
    ∀ j, (programs j).compile.evaluationStorageWithWorkspace input.environment ≤ parameterStorageBound s := by
  have hc := input_canonical input hC
  have hi := input_environment input source hR
  have hh : ∀ j, RationalHeight (value (input.environment.read j)) (expressionHeightBudget s 12) := by
    intro j
    have he := (hHeight j).mono (expressionHeightBudget_ge_input s 12)
    rw [← hi] at he
    simpa only [BinaryRationalExpression.interpretedEnvironment,FixedArrayTable.read_ofFn] using he
  intro j
  have he := (programs j).compile.evaluationStorageWithWorkspace_bound input.environment hc (programs j).compile_canonical _
    (by rw [programs_interpreted,hi]; exact RationalFourParametersCode.intermediates source j s hs hHeight) hh
  rw [(programs j).compile.depth_interpreted,programs_interpreted] at he
  have hd := RationalFourParametersCode.depth j
  have hn := (compiled_sizes j).2.1
  have hl := (compiled_sizes j).2.2
  have ho := RationalFourParametersCode.operationBound j
  have hTerm : (programs j).compile.literalCount + 3 * ((RationalFourParametersCode.programs j).depth + 1) ≤ 295 := by omega
  have hControl : (RationalFourParametersCode.programs j).depth + (programs j).compile.syntaxNodes + 2 ≤ 270 := by omega
  unfold parameterStorageBound
  exact he.trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right _ hTerm) _)
    (Nat.mul_le_mul_left 4 hControl)) (Nat.mul_le_mul_right _ ho))

end Blotto.BinaryFourParameters
