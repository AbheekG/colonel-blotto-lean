import Blotto.BinaryExpressionCompiler
import Blotto.RationalOverlapFormulaHeight

/-! The actual retained overlap formulas are compiled from explicit Boolean
zero/one literals. The emitted AST has exactly the retained source shape and
conditional/total-division semantics; no literal encoder or compiler oracle is
assumed. Inputs are existing canonical Boolean words whose rational values
match the sixteen retained endpoint/weight/budget inputs. Their parsing and
preparation, opcode scratch and the full PRG controller remain separate. -/

namespace Blotto.BinaryOverlapCompilerBridge
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler

abbrev Expr := Syntax 16

def firstP (j : Fin 3) : Expr := .input ⟨j.val, by omega⟩
def firstQ (j : Fin 3) : Expr := .input ⟨3 + j.val, by omega⟩
def secondP (j : Fin 3) : Expr := .input ⟨6 + j.val, by omega⟩
def secondQ (j : Fin 3) : Expr := .input ⟨9 + j.val, by omega⟩
def firstWeight : Expr := .input 12
def secondWeight : Expr := .input 13
def intervalLength : Expr := .input 14
def budget : Expr := .input 15
def absolute (e : Expr) : Expr := .maximum e (.sub (.literal .zero) e)
def reflectedP : Expr := .sub intervalLength (secondP 0)
def reflectedQ : Expr := .sub intervalLength (secondQ 0)
def lower : Expr := .maximum (.minimum (firstP 2) (firstQ 2)) (.minimum reflectedP reflectedQ)
def upper : Expr := .minimum (.maximum (firstP 2) (firstQ 2)) (.maximum reflectedP reflectedQ)
def weight : Expr :=
  .div (.mul (.mul (.mul intervalLength firstWeight) secondWeight)
      (.maximum (.sub upper lower) (.literal .zero)))
    (.mul (absolute (.sub (firstQ 2) (firstP 2))) (absolute (.sub reflectedQ reflectedP)))
def firstInverse (z : Expr) : Expr := .div (.sub z (firstP 2)) (.sub (firstQ 2) (firstP 2))
def secondInverse (z : Expr) : Expr := .div (.sub z reflectedP) (.sub reflectedQ reflectedP)
def interpolate (a b t : Expr) : Expr := .add (.mul (.sub (.literal .one) t) a) (.mul t b)
def curve (z : Expr) : Fin 4 → Expr :=
  ![interpolate (firstP 0) (firstQ 0) (firstInverse z),
    interpolate (firstP 1) (firstQ 1) (firstInverse z),
    interpolate (secondP 1) (secondQ 1) (secondInverse z),
    interpolate (secondP 2) (secondQ 2) (secondInverse z)]
def fallback : Fin 4 → Expr := ![budget, .literal .zero, .literal .zero, .literal .zero]
def safeP (j : Fin 4) : Expr := .ifLe weight (.literal .zero) (fallback j) (curve lower j)
def safeQ (j : Fin 4) : Expr := .ifLe weight (.literal .zero) (fallback j) (curve upper j)

theorem weight_source : weight.rational = OverlapFormulaCode.weight := rfl
theorem safeP_source (r : Fin 4) : (safeP r).rational = OverlapFormulaCode.safeP r := by fin_cases r <;> rfl
theorem safeQ_source (r : Fin 4) : (safeQ r).rational = OverlapFormulaCode.safeQ r := by fin_cases r <;> rfl

theorem weight_interpreted : weight.compile.interpreted = OverlapFormulaCode.weight :=
  weight.compile_interpreted.trans weight_source
theorem safeP_interpreted (r : Fin 4) : (safeP r).compile.interpreted = OverlapFormulaCode.safeP r :=
  (safeP r).compile_interpreted.trans (safeP_source r)
theorem safeQ_interpreted (r : Fin 4) : (safeQ r).compile.interpreted = OverlapFormulaCode.safeQ r :=
  (safeQ r).compile_interpreted.trans (safeQ_source r)

theorem compiled_fixed_size : weight.nodes ≤ 128 ∧
    (∀ r, (safeP r).nodes ≤ 256) ∧ (∀ r, (safeQ r).nodes ≤ 256) := by
  constructor
  · decide
  · constructor <;> intro r <;> fin_cases r <;> decide

theorem compiled_allocation : weight.compileAllocated ≤ 768 ∧
    (∀ r, (safeP r).compileAllocated ≤ 1536) ∧ (∀ r, (safeQ r).compileAllocated ≤ 1536) := by
  have h := compiled_fixed_size
  refine ⟨(weight.compileAllocated_bound).trans (Nat.mul_le_mul_left 6 h.1), ?_, ?_⟩
  · intro r; exact ((safeP r).compileAllocated_bound).trans (Nat.mul_le_mul_left 6 (h.2.1 r))
  · intro r; exact ((safeQ r).compileAllocated_bound).trans (Nat.mul_le_mul_left 6 (h.2.2 r))

theorem weight_native_value (env : FixedArrayTable 16 SignedWord)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j)) :
    value (weight.compile.run env).1 =
      OverlapFormulaCode.weight.value (BinaryRationalExpression.interpretedEnvironment env) := by
  have h := weight.compile_run_value env hEnv
  rw [weight_source] at h
  exact h

theorem safeP_native_value (r : Fin 4) (env : FixedArrayTable 16 SignedWord)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j)) :
    value ((safeP r).compile.run env).1 =
      (OverlapFormulaCode.safeP r).value (BinaryRationalExpression.interpretedEnvironment env) := by
  have h := (safeP r).compile_run_value env hEnv
  rw [safeP_source] at h
  exact h

theorem safeQ_native_value (r : Fin 4) (env : FixedArrayTable 16 SignedWord)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j)) :
    value ((safeQ r).compile.run env).1 =
      (OverlapFormulaCode.safeQ r).value (BinaryRationalExpression.interpretedEnvironment env) := by
  have h := (safeQ r).compile_run_value env hEnv
  rw [safeQ_source] at h
  exact h

theorem compiled_bitWork (env : FixedArrayTable 16 SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ j, RationalHeight (value (env.read j)) s) :
    weight.compile.bitWork env ≤ 128 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 7) ∧
      (∀ r, (safeP r).compile.bitWork env ≤ 256 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 9)) ∧
      (∀ r, (safeQ r).compile.bitWork env ≤ 256 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 9)) := by
  have hEnvHeight : ∀ j, RationalHeight ((BinaryRationalExpression.interpretedEnvironment env).read j) s := by
    intro j
    simpa only [BinaryRationalExpression.interpretedEnvironment, FixedArrayTable.read_ofFn] using hHeight j
  have hw := weight.compile.bitWork_bound env hEnv weight.compile_canonical
    (expressionHeightBudget s 7) (by rw [weight_interpreted]; exact OverlapFormulaCode.weight_intermediates _ s hs hEnvHeight)
  rw [weight_interpreted] at hw
  refine ⟨hw.trans (Nat.mul_le_mul_right _ OverlapFormulaCode.weight_operationBound), ?_, ?_⟩
  · intro r
    have h := (safeP r).compile.bitWork_bound env hEnv (safeP r).compile_canonical
      (expressionHeightBudget s 9) (by rw [safeP_interpreted]; exact OverlapFormulaCode.safeP_intermediates r _ s hs hEnvHeight)
    rw [safeP_interpreted] at h
    exact h.trans (Nat.mul_le_mul_right _ (OverlapFormulaCode.safeP_operationBound r))
  · intro r
    have h := (safeQ r).compile.bitWork_bound env hEnv (safeQ r).compile_canonical
      (expressionHeightBudget s 9) (by rw [safeQ_interpreted]; exact OverlapFormulaCode.safeQ_intermediates r _ s hs hEnvHeight)
    rw [safeQ_interpreted] at h
    exact h.trans (Nat.mul_le_mul_right _ (OverlapFormulaCode.safeQ_operationBound r))

theorem compiled_canonical_outputs (env : FixedArrayTable 16 SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) :
    CanonicalWord (weight.compile.run env).1 ∧
      (∀ r, CanonicalWord ((safeP r).compile.run env).1) ∧
      (∀ r, CanonicalWord ((safeQ r).compile.run env).1) :=
  ⟨weight.compile.run_canonical env hEnv weight.compile_canonical,
    fun r => (safeP r).compile.run_canonical env hEnv (safeP r).compile_canonical,
    fun r => (safeQ r).compile.run_canonical env hEnv (safeQ r).compile_canonical⟩

theorem compiled_control_depth (env : FixedArrayTable 16 SignedWord) :
    (weight.compile.runWithStorage env).2.2 ≤ 8 ∧
      (∀ r, ((safeP r).compile.runWithStorage env).2.2 ≤ 10) ∧
      (∀ r, ((safeQ r).compile.runWithStorage env).2.2 ≤ 10) := by
  have hw := weight.compile.controlDepth_bound env
  rw [weight.compile.depth_interpreted, weight_interpreted] at hw
  have hd := OverlapFormulaCode.weight_depth
  refine ⟨hw.trans (by omega), ?_, ?_⟩
  · intro r
    have h := (safeP r).compile.controlDepth_bound env
    rw [(safeP r).compile.depth_interpreted, safeP_interpreted] at h
    have hd := OverlapFormulaCode.safeP_depth r
    omega
  · intro r
    have h := (safeQ r).compile.controlDepth_bound env
    rw [(safeQ r).compile.depth_interpreted, safeQ_interpreted] at h
    have hd := OverlapFormulaCode.safeQ_depth r
    omega

theorem compiled_selected_payload (env : FixedArrayTable 16 SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ j, RationalHeight (value (env.read j)) s) :
    (weight.compile.runWithStorage env).2.1 ≤ 24 * (8 * expressionHeightBudget s 7 + 7) ∧
      (∀ r, ((safeP r).compile.runWithStorage env).2.1 ≤ 30 * (8 * expressionHeightBudget s 9 + 7)) ∧
      (∀ r, ((safeQ r).compile.runWithStorage env).2.1 ≤ 30 * (8 * expressionHeightBudget s 9 + 7)) := by
  have hEnvHeight : ∀ j, RationalHeight ((BinaryRationalExpression.interpretedEnvironment env).read j) s := by
    intro j
    simpa only [BinaryRationalExpression.interpretedEnvironment, FixedArrayTable.read_ofFn] using hHeight j
  have hw := weight.compile.resultPeak_height_bound env hEnv weight.compile_canonical
    (expressionHeightBudget s 7) (by rw [weight_interpreted]; exact OverlapFormulaCode.weight_intermediates _ s hs hEnvHeight)
  rw [weight.compile.depth_interpreted, weight_interpreted] at hw
  have hd := OverlapFormulaCode.weight_depth
  refine ⟨hw.trans (Nat.mul_le_mul_right _ (by omega)), ?_, ?_⟩
  · intro r
    have h := (safeP r).compile.resultPeak_height_bound env hEnv (safeP r).compile_canonical
      (expressionHeightBudget s 9) (by rw [safeP_interpreted]; exact OverlapFormulaCode.safeP_intermediates r _ s hs hEnvHeight)
    rw [(safeP r).compile.depth_interpreted, safeP_interpreted] at h
    have hd := OverlapFormulaCode.safeP_depth r
    exact h.trans (Nat.mul_le_mul_right _ (by omega))
  · intro r
    have h := (safeQ r).compile.resultPeak_height_bound env hEnv (safeQ r).compile_canonical
      (expressionHeightBudget s 9) (by rw [safeQ_interpreted]; exact OverlapFormulaCode.safeQ_intermediates r _ s hs hEnvHeight)
    rw [(safeQ r).compile.depth_interpreted, safeQ_interpreted] at h
    have hd := OverlapFormulaCode.safeQ_depth r
    exact h.trans (Nat.mul_le_mul_right _ (by omega))

-- This equality is an input-data refinement contract, not an encoder callback.
-- It can be established from actual framed Boolean input words before execution.
theorem gluing_values {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (env : FixedArrayTable 16 SignedWord) (hEnv : ∀ r, BinaryRationalOpcode.Valid (env.read r))
    (hInputs : BinaryRationalExpression.interpretedEnvironment env = RationalOverlapFormula.environment G B i j) :
    value (weight.compile.run env).1 = G.weight i j ∧
      (∀ r, value ((safeP r).compile.run env).1 = G.safeP B i j r) ∧
      (∀ r, value ((safeQ r).compile.run env).1 = G.safeQ B i j r) := by
  constructor
  · rw [weight_native_value env hEnv, hInputs]
    exact RationalOverlapFormula.weight_value G B i j
  · constructor
    · intro r
      rw [safeP_native_value r env hEnv, hInputs]
      exact RationalOverlapFormula.safeP_value G B i j r
    · intro r
      rw [safeQ_native_value r env hEnv, hInputs]
      exact RationalOverlapFormula.safeQ_value G B i j r

end Blotto.BinaryOverlapCompilerBridge
