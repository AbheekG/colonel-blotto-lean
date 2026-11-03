import Blotto.BinaryThreeDescriptorCompiler
import Blotto.RationalNestedResidualCode

/-! The nested middle case produces its actual three-slot stored Boolean
segment lottery directly from five stored geometry/location words. Native
expressions use only the explicit zero literal and agree with the retained
residual source formulas, including zero-weight slots. Work and workspace use
the existing abstract Boolean/list-cell model; full controller pricing and
physical compiler allocation remain separate. -/

namespace Blotto.BinaryNestedResidualCompiler
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler
open scoped BigOperators

abbrev Expr := Syntax 5
def U : Expr := .input 0
def V : Expr := .input 1
def W : Expr := .input 2
def H : Expr := .input 3
def T : Expr := .input 4
def A : Expr := .add (.add V W) H
def D : Expr := .add (.add U W) H
def C : Expr := .add (.add U V) H
def G : Expr := .add V H
def S : Expr := .sub U T
def denominator : Expr := .add (.mul G D) (.mul W S)
def weights : Fin 3 → Expr :=
  ![.div (.mul W S) denominator, .div (.mul G (.sub D S)) denominator, .div (.mul G S) denominator]
def vertices : Fin 3 → Fin 3 → Expr :=
  ![![.literal .zero, D, V], ![W, .literal .zero, C], ![A, S, T]]

theorem weight_source (slot : Fin 3) : (weights slot).rational = RationalNestedResidualCode.weights slot := by
  fin_cases slot <;> rfl

theorem vertex_source (slot j : Fin 3) : (vertices slot j).rational = RationalNestedResidualCode.vertices slot j := by
  fin_cases slot <;> fin_cases j <;> rfl

theorem weight_interpreted (slot : Fin 3) : (weights slot).compile.interpreted = RationalNestedResidualCode.weights slot :=
  (weights slot).compile_interpreted.trans (weight_source slot)

theorem vertex_interpreted (slot j : Fin 3) : (vertices slot j).compile.interpreted = RationalNestedResidualCode.vertices slot j :=
  (vertices slot j).compile_interpreted.trans (vertex_source slot j)

theorem compiled_sizes :
    (∀ slot, (weights slot).compileAllocated ≤ 768 ∧ (weights slot).compile.syntaxNodes ≤ 128 ∧
      (weights slot).compile.literalCount ≤ 128) ∧
    (∀ slot j, (vertices slot j).compileAllocated ≤ 96 ∧ (vertices slot j).compile.syntaxNodes ≤ 16 ∧
      (vertices slot j).compile.literalCount ≤ 16) := by
  constructor
  · intro slot; fin_cases slot <;> decide
  · intro slot j; fin_cases slot <;> fin_cases j <;> decide

def descriptor (env : FixedArrayTable 5 SignedWord) : BinaryStoredOverlapEnvironment.Segment 3 3 where
  weight := FixedArrayTable.ofFn (fun slot => ((weights slot).compile.run env).1)
  P := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j =>
    ((vertices (RationalNestedResidual.edges slot).1 j).compile.run env).1))
  Q := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j =>
    ((vertices (RationalNestedResidual.edges slot).2 j).compile.run env).1))

theorem descriptor_canonical (env : FixedArrayTable 5 SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) : (descriptor env).Canonical := by
  constructor
  · intro slot
    simp only [descriptor, FixedArrayTable.read_ofFn]
    exact (weights slot).compile.run_canonical env hEnv (weights slot).compile_canonical
  · constructor
    · intro slot j
      simp only [descriptor, FixedArrayTable.read_ofFn]
      exact (vertices _ j).compile.run_canonical env hEnv (vertices _ j).compile_canonical
    · intro slot j
      simp only [descriptor, FixedArrayTable.read_ofFn]
      exact (vertices _ j).compile.run_canonical env hEnv (vertices _ j).compile_canonical

theorem descriptor_refines (env : FixedArrayTable 5 SignedWord) (r : RationalNestedResidual)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j))
    (hInputs : BinaryRationalExpression.interpretedEnvironment env = RationalNestedResidualCode.environment r) :
    (descriptor env).Refines r.segmentLottery := by
  constructor
  · intro slot
    simp only [descriptor, FixedArrayTable.read_ofFn]
    have he := (weights slot).compile_run_value env hEnv
    rw [weight_source, hInputs] at he
    exact he.trans (RationalNestedResidualCode.weight_value r slot)
  · constructor
    · intro slot j
      simp only [descriptor, FixedArrayTable.read_ofFn]
      have he := (vertices (RationalNestedResidual.edges slot).1 j).compile_run_value env hEnv
      rw [vertex_source, hInputs] at he
      exact he.trans (RationalNestedResidualCode.vertex_value r _ j)
    · intro slot j
      simp only [descriptor, FixedArrayTable.read_ofFn]
      have he := (vertices (RationalNestedResidual.edges slot).2 j).compile_run_value env hEnv
      rw [vertex_source, hInputs] at he
      exact he.trans (RationalNestedResidualCode.vertex_value r _ j)

-- This retained source already proves all weight intermediates. The following
-- derives the analogous vertex premise directly from source depth/literals.
theorem vertex_intermediates (r : RationalNestedResidual) (slot j : Fin 3) (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ k, RationalHeight ((RationalNestedResidualCode.environment r).read k) s) :
    (RationalNestedResidualCode.vertices slot j).AllRunHeights (RationalNestedResidualCode.environment r)
      (expressionHeightBudget s 3) := by
  have he := (RationalNestedResidualCode.vertices slot j).run_all_heights _ s hHeight
    ((RationalNestedResidualCode.vertices slot j).LiteralHeights_mono hs
      (RationalNestedResidualCode.vertex_literals slot j))
  exact RationalExpression.AllRunHeights_mono _ _
    (expressionHeightBudget_mono s (RationalNestedResidualCode.vertex_depth slot j)) he

def descriptorWork (env : FixedArrayTable 5 SignedWord) : ℕ :=
  (∑ slot : Fin 3, (weights slot).compile.bitWork env) +
    (∑ slot : Fin 3, ∑ j : Fin 3,
      (vertices (RationalNestedResidual.edges slot).1 j).compile.bitWork env) +
    (∑ slot : Fin 3, ∑ j : Fin 3,
      (vertices (RationalNestedResidual.edges slot).2 j).compile.bitWork env) + 1000

def descriptorWithWork (env : FixedArrayTable 5 SignedWord) : BinaryStoredOverlapEnvironment.Segment 3 3 × ℕ :=
  (descriptor env, descriptorWork env)

theorem descriptorWithWork_state (env : FixedArrayTable 5 SignedWord) :
    (descriptorWithWork env).1 = descriptor env := rfl

theorem descriptorWork_bound (env : FixedArrayTable 5 SignedWord) (r : RationalNestedResidual)
    (hEnv : ∀ j, CanonicalWord (env.read j))
    (hInputs : BinaryRationalExpression.interpretedEnvironment env = RationalNestedResidualCode.environment r)
    (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ j, RationalHeight ((RationalNestedResidualCode.environment r).read j) s) :
    descriptorWork env ≤ 384 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 8) +
      288 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 3) + 1000 := by
  have hw : ∀ slot, (weights slot).compile.bitWork env ≤
      128 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 8) := by
    intro slot
    have he := (weights slot).compile.bitWork_bound env hEnv (weights slot).compile_canonical
      (expressionHeightBudget s 8) (by
        rw [weight_interpreted, hInputs]
        exact RationalNestedResidualCode.weight_intermediates r slot s hs hHeight)
    rw [weight_interpreted] at he
    exact he.trans (Nat.mul_le_mul_right _ (RationalNestedResidualCode.weight_operationBound slot))
  have hv : ∀ slot j, (vertices slot j).compile.bitWork env ≤
      16 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 3) := by
    intro slot j
    have he := (vertices slot j).compile.bitWork_bound env hEnv (vertices slot j).compile_canonical
      (expressionHeightBudget s 3) (by
        rw [vertex_interpreted, hInputs]
        exact vertex_intermediates r slot j s hs hHeight)
    rw [vertex_interpreted] at he
    exact he.trans (Nat.mul_le_mul_right _ (RationalNestedResidualCode.vertex_operationBound slot j))
  have hwSum : (∑ slot : Fin 3, (weights slot).compile.bitWork env) ≤
      384 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 8) :=
    (Finset.sum_le_sum (fun slot _ => hw slot)).trans_eq (by simp; ring)
  have hpSum : (∑ slot : Fin 3, ∑ j : Fin 3,
      (vertices (RationalNestedResidual.edges slot).1 j).compile.bitWork env) ≤
      144 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 3) :=
    (Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hv _ j))).trans_eq (by simp; ring)
  have hqSum : (∑ slot : Fin 3, ∑ j : Fin 3,
      (vertices (RationalNestedResidual.edges slot).2 j).compile.bitWork env) ≤
      144 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 3) :=
    (Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hv _ j))).trans_eq (by simp; ring)
  unfold descriptorWork
  omega

theorem descriptor_primitive_workspace (env : FixedArrayTable 5 SignedWord) (r : RationalNestedResidual)
    (hEnv : ∀ j, CanonicalWord (env.read j))
    (hInputs : BinaryRationalExpression.interpretedEnvironment env = RationalNestedResidualCode.environment r)
    (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ j, RationalHeight ((RationalNestedResidualCode.environment r).read j) s) :
    (∀ slot, (weights slot).compile.primitiveWorkspace env ≤
      128 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 8)) ∧
    (∀ slot j, (vertices slot j).compile.primitiveWorkspace env ≤
      16 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 3)) := by
  constructor
  · intro slot
    have he := (weights slot).compile.primitiveWorkspace_bound env hEnv (weights slot).compile_canonical
      (expressionHeightBudget s 8) (by
        rw [weight_interpreted, hInputs]
        exact RationalNestedResidualCode.weight_intermediates r slot s hs hHeight)
    rw [weight_interpreted] at he
    exact he.trans (Nat.mul_le_mul_right _ (RationalNestedResidualCode.weight_operationBound slot))
  · intro slot j
    have he := (vertices slot j).compile.primitiveWorkspace_bound env hEnv (vertices slot j).compile_canonical
      (expressionHeightBudget s 3) (by
        rw [vertex_interpreted, hInputs]
        exact vertex_intermediates r slot j s hs hHeight)
    rw [vertex_interpreted] at he
    exact he.trans (Nat.mul_le_mul_right _ (RationalNestedResidualCode.vertex_operationBound slot j))

def weightStorageBound (s : ℕ) : ℕ :=
  5 * (4 * expressionHeightBudget s 8 + 3) + 155 * (8 * expressionHeightBudget s 8 + 7) +
    4 * 138 + 128 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 8)

def vertexStorageBound (s : ℕ) : ℕ :=
  5 * (4 * expressionHeightBudget s 3 + 3) + 28 * (8 * expressionHeightBudget s 3 + 7) +
    4 * 21 + 16 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 3)

theorem descriptor_evaluation_storage (env : FixedArrayTable 5 SignedWord) (r : RationalNestedResidual)
    (hEnv : ∀ j, CanonicalWord (env.read j))
    (hInputs : BinaryRationalExpression.interpretedEnvironment env = RationalNestedResidualCode.environment r)
    (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ j, RationalHeight ((RationalNestedResidualCode.environment r).read j) s) :
    (∀ slot, (weights slot).compile.evaluationStorageWithWorkspace env ≤ weightStorageBound s) ∧
      (∀ slot j, (vertices slot j).compile.evaluationStorageWithWorkspace env ≤ vertexStorageBound s) := by
  have hEnvHeight : ∀ j, RationalHeight (value (env.read j)) s := by
    intro j
    have he := hHeight j
    rw [← hInputs] at he
    simpa only [BinaryRationalExpression.interpretedEnvironment, FixedArrayTable.read_ofFn] using he
  constructor
  · intro slot
    have hh : ∀ j, RationalHeight (value (env.read j)) (expressionHeightBudget s 8) := fun j =>
      (hEnvHeight j).mono (expressionHeightBudget_ge_input s 8)
    have he := (weights slot).compile.evaluationStorageWithWorkspace_bound env hEnv
      (weights slot).compile_canonical (expressionHeightBudget s 8) (by
        rw [weight_interpreted, hInputs]
        exact RationalNestedResidualCode.weight_intermediates r slot s hs hHeight) hh
    rw [(weights slot).compile.depth_interpreted, weight_interpreted] at he
    have hd := RationalNestedResidualCode.weight_depth slot
    have hn := (compiled_sizes.1 slot).2.1
    have hl := (compiled_sizes.1 slot).2.2
    have ho := RationalNestedResidualCode.weight_operationBound slot
    have hTerm : (weights slot).compile.literalCount +
        3 * ((RationalNestedResidualCode.weights slot).depth + 1) ≤ 155 := by omega
    have hControl : (RationalNestedResidualCode.weights slot).depth +
        (weights slot).compile.syntaxNodes + 2 ≤ 138 := by omega
    unfold weightStorageBound
    exact he.trans (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hTerm) _)
      (Nat.mul_le_mul_left 4 hControl)) (Nat.mul_le_mul_right _ ho))
  · intro slot j
    have hh : ∀ k, RationalHeight (value (env.read k)) (expressionHeightBudget s 3) := fun k =>
      (hEnvHeight k).mono (expressionHeightBudget_ge_input s 3)
    have he := (vertices slot j).compile.evaluationStorageWithWorkspace_bound env hEnv
      (vertices slot j).compile_canonical (expressionHeightBudget s 3) (by
        rw [vertex_interpreted, hInputs]
        exact vertex_intermediates r slot j s hs hHeight) hh
    rw [(vertices slot j).compile.depth_interpreted, vertex_interpreted] at he
    have hd := RationalNestedResidualCode.vertex_depth slot j
    have hn := (compiled_sizes.2 slot j).2.1
    have hl := (compiled_sizes.2 slot j).2.2
    have ho := RationalNestedResidualCode.vertex_operationBound slot j
    have hTerm : (vertices slot j).compile.literalCount +
        3 * ((RationalNestedResidualCode.vertices slot j).depth + 1) ≤ 28 := by omega
    have hControl : (RationalNestedResidualCode.vertices slot j).depth +
        (vertices slot j).compile.syntaxNodes + 2 ≤ 21 := by omega
    unfold vertexStorageBound
    exact he.trans (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hTerm) _)
      (Nat.mul_le_mul_left 4 hControl)) (Nat.mul_le_mul_right _ ho))

end Blotto.BinaryNestedResidualCompiler
