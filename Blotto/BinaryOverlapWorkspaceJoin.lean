import Blotto.BinaryExpressionWorkspace
import Blotto.BinaryOverlapCompilerBridge

/-! Concrete compiled overlap expressions include their selected Boolean
opcode/comparator workspace, static AST/literal payload, environment and live
result/control storage. Bounds follow the retained fixed-depth source formulas
and their input heights; no primitive scratch or literal compiler oracle is
supplied. Sixteen-input parsing/preparation and physical GC remain separate. -/

namespace Blotto.BinaryOverlapCompilerBridge
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler

theorem compiled_syntax_bounds : weight.compile.syntaxNodes ≤ 128 ∧
    (∀ r, (safeP r).compile.syntaxNodes ≤ 256) ∧ (∀ r, (safeQ r).compile.syntaxNodes ≤ 256) := by
  constructor
  · decide
  · constructor <;> intro r <;> fin_cases r <;> decide

theorem compiled_literal_bounds : weight.compile.literalCount ≤ 128 ∧
    (∀ r, (safeP r).compile.literalCount ≤ 256) ∧ (∀ r, (safeQ r).compile.literalCount ≤ 256) := by
  constructor
  · decide
  · constructor <;> intro r <;> fin_cases r <;> decide

def weightStorageBound (s : ℕ) : ℕ :=
  16 * (4 * expressionHeightBudget s 7 + 3) +
    152 * (8 * expressionHeightBudget s 7 + 7) + 4 * 137 +
    128 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 7)

def endpointStorageBound (s : ℕ) : ℕ :=
  16 * (4 * expressionHeightBudget s 9 + 3) +
    286 * (8 * expressionHeightBudget s 9 + 7) + 4 * 267 +
    256 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 9)

theorem compiled_workspace_bound (env : FixedArrayTable 16 SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ j, RationalHeight (value (env.read j)) s) :
    weight.compile.evaluationStorageWithWorkspace env ≤ weightStorageBound s ∧
      (∀ r, (safeP r).compile.evaluationStorageWithWorkspace env ≤ endpointStorageBound s) ∧
      (∀ r, (safeQ r).compile.evaluationStorageWithWorkspace env ≤ endpointStorageBound s) := by
  have hEnvHeight : ∀ j, RationalHeight ((BinaryRationalExpression.interpretedEnvironment env).read j) s := by
    intro j
    simpa only [BinaryRationalExpression.interpretedEnvironment, FixedArrayTable.read_ofFn] using hHeight j
  have h7 : ∀ j, RationalHeight (value (env.read j)) (expressionHeightBudget s 7) := fun j =>
    (hHeight j).mono (by simpa only [expressionHeightBudget_zero] using expressionHeightBudget_mono s (show 0 ≤ 7 by omega))
  have h9 : ∀ j, RationalHeight (value (env.read j)) (expressionHeightBudget s 9) := fun j =>
    (hHeight j).mono (by simpa only [expressionHeightBudget_zero] using expressionHeightBudget_mono s (show 0 ≤ 9 by omega))
  have hn := compiled_syntax_bounds
  have hl := compiled_literal_bounds
  have hw := weight.compile.evaluationStorageWithWorkspace_bound env hEnv weight.compile_canonical
    (expressionHeightBudget s 7) (by rw [weight_interpreted]; exact OverlapFormulaCode.weight_intermediates _ s hs hEnvHeight) h7
  rw [weight.compile.depth_interpreted, weight_interpreted] at hw
  have hd := OverlapFormulaCode.weight_depth
  refine ⟨hw.trans ?_, ?_, ?_⟩
  · unfold weightStorageBound
    have hOp := OverlapFormulaCode.weight_operationBound
    have hTerm : weight.compile.literalCount + 3 * (OverlapFormulaCode.weight.depth + 1) ≤ 152 := by omega
    have hControl : OverlapFormulaCode.weight.depth + weight.compile.syntaxNodes + 2 ≤ 137 := by omega
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right _ hTerm) _)
      (Nat.mul_le_mul_left 4 hControl)) (Nat.mul_le_mul_right _ hOp)
  · intro r
    have h := (safeP r).compile.evaluationStorageWithWorkspace_bound env hEnv (safeP r).compile_canonical
      (expressionHeightBudget s 9) (by rw [safeP_interpreted]; exact OverlapFormulaCode.safeP_intermediates r _ s hs hEnvHeight) h9
    rw [(safeP r).compile.depth_interpreted, safeP_interpreted] at h
    have hd := OverlapFormulaCode.safeP_depth r
    have hOp := OverlapFormulaCode.safeP_operationBound r
    have hN := hn.2.1 r
    have hL := hl.2.1 r
    have hTerm : (safeP r).compile.literalCount + 3 * ((OverlapFormulaCode.safeP r).depth + 1) ≤ 286 := by omega
    have hControl : (OverlapFormulaCode.safeP r).depth + (safeP r).compile.syntaxNodes + 2 ≤ 267 := by omega
    unfold endpointStorageBound
    exact h.trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right _ hTerm) _)
      (Nat.mul_le_mul_left 4 hControl)) (Nat.mul_le_mul_right _ hOp))
  · intro r
    have h := (safeQ r).compile.evaluationStorageWithWorkspace_bound env hEnv (safeQ r).compile_canonical
      (expressionHeightBudget s 9) (by rw [safeQ_interpreted]; exact OverlapFormulaCode.safeQ_intermediates r _ s hs hEnvHeight) h9
    rw [(safeQ r).compile.depth_interpreted, safeQ_interpreted] at h
    have hd := OverlapFormulaCode.safeQ_depth r
    have hOp := OverlapFormulaCode.safeQ_operationBound r
    have hN := hn.2.2 r
    have hL := hl.2.2 r
    have hTerm : (safeQ r).compile.literalCount + 3 * ((OverlapFormulaCode.safeQ r).depth + 1) ≤ 286 := by omega
    have hControl : (OverlapFormulaCode.safeQ r).depth + (safeQ r).compile.syntaxNodes + 2 ≤ 267 := by omega
    unfold endpointStorageBound
    exact h.trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right _ hTerm) _)
      (Nat.mul_le_mul_left 4 hControl)) (Nat.mul_le_mul_right _ hOp))

theorem compiled_workspace_execution (env : FixedArrayTable 16 SignedWord) :
    (weight.compile.runWithWorkspace env).1 = weight.compile.run env ∧
      (∀ r, ((safeP r).compile.runWithWorkspace env).1 = (safeP r).compile.run env) ∧
      (∀ r, ((safeQ r).compile.runWithWorkspace env).1 = (safeQ r).compile.run env) := by
  simp only [BinaryRationalExpression.runWithWorkspace_refines, and_self]
  exact ⟨trivial, fun _ => trivial⟩

theorem gluing_workspace_contract {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (env : FixedArrayTable 16 SignedWord) (hEnv : ∀ r, CanonicalWord (env.read r))
    (hInputs : BinaryRationalExpression.interpretedEnvironment env = RationalOverlapFormula.environment G B i j)
    (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    value (weight.compile.runWithWorkspace env).1.1 = G.weight i j ∧
      (∀ r, value ((safeP r).compile.runWithWorkspace env).1.1 = G.safeP B i j r) ∧
      (∀ r, value ((safeQ r).compile.runWithWorkspace env).1.1 = G.safeQ B i j r) ∧
      weight.compile.evaluationStorageWithWorkspace env ≤ weightStorageBound s ∧
      (∀ r, (safeP r).compile.evaluationStorageWithWorkspace env ≤ endpointStorageBound s) ∧
      (∀ r, (safeQ r).compile.evaluationStorageWithWorkspace env ≤ endpointStorageBound s) := by
  have hValues := gluing_values G B i j env (fun r => (hEnv r).1) hInputs
  have hHeight : ∀ r, RationalHeight (value (env.read r)) s := by
    intro r
    have hh := RationalOverlapFormula.environment_height G B i j s hFirst hSecond hD hB r
    rw [← hInputs] at hh
    simpa only [BinaryRationalExpression.interpretedEnvironment, FixedArrayTable.read_ofFn] using hh
  have hStorage := compiled_workspace_bound env hEnv s hs hHeight
  simp only [BinaryRationalExpression.runWithWorkspace_refines]
  exact ⟨hValues.1, hValues.2.1, hValues.2.2, hStorage.1, hStorage.2.1, hStorage.2.2⟩

end Blotto.BinaryOverlapCompilerBridge
