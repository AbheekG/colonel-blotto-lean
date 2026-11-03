import Blotto.BinaryStoredOverlapEnvironment
import Blotto.RationalThreeCodeIntermediates

/-! The regular three-variable parent descriptor is produced by actual Boolean
expression evaluation from four stored geometry words. Explicit 0/1/2 literals
and all selected weight branches agree with the retained portable source AST.
Every field of the native 3-by-9 segment table is canonical, with derived work
and primitive workspace bounds. Source input/regime preparation is separate. -/

namespace Blotto.BinaryThreeDescriptorCompiler
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler
open scoped BigOperators

abbrev Expr := Syntax 4
def U : Expr := .input 0
def V : Expr := .input 1
def W : Expr := .input 2
def H : Expr := .input 3
def A : Expr := .add (.add V W) H
def D : Expr := .add (.add U W) H
def C : Expr := .add (.add U V) H
def E : Expr := .add W H
def F : Expr := .add U H
def G : Expr := .add V H
def power (e : Expr) : ℕ → Expr
  | 0 => .literal .one
  | n + 1 => .mul (power e n) e
def R : Expr := .add (.add (power H 2) (.mul H (.add U W))) (.mul W (.add U V))
def S : Expr := .add (.add (.add (.add (power H 3)
  (.mul (.add (.add U V) W) (power H 2)))
  (.mul (.add (.add (.mul U V) (.mul U W)) (.mul V W)) H))
  (.mul (.mul U V) W)) (.mul (power V 2) W)
def first : Fin 9 → Expr :=
  ![(.div (.mul (.mul W G) R) (.mul (.mul (.mul A C) E) F)),
    (.div (.mul (.mul (.sub U W) G) R) (.mul (.mul (.mul A C) E) F)),
    (.literal .zero), (.literal .zero),
    (.div (.mul (.sub V W) H) (.mul C E)),
    (.div (.mul W H) (.mul C E)),
    (.div (.mul (.mul W (.sub U V)) R) (.mul (.mul (.mul A C) E) F)),
    (.div H C),
    (.div (.mul (.mul V W) (.add (.add U V) (.mul (.literal .two) H))) (.mul (.mul A C) F))]
def second : Fin 9 → Expr :=
  ![(.div (.mul W G) (.mul A F)),
    (.div (.mul (.sub U W) S) (.mul (.mul (.mul A C) E) F)),
    (.div (.mul V H) (.mul C E)),
    (.literal .zero), (.literal .zero), (.literal .zero),
    (.div (.mul W (.sub U V)) (.mul A F)), (.div H C), (.div (.mul V W) (.mul A F))]
def third : Fin 9 → Expr :=
  ![(.literal .zero), (.div (.mul V (.sub W U)) (.mul C E)),
    (.div (.mul V F) (.mul C E)), (.div (.mul U G) (.mul C E)),
    (.div (.mul U (.sub W V)) (.mul C E)), (.literal .zero), (.literal .zero),
    (.div H C), (.literal .zero)]
def chosen (slot : Fin 9) : Expr := .ifLe W V (first slot) (.ifLe W U (second slot) (third slot))
def vertex : Fin 6 → Fin 3 → Expr :=
  ![![.literal .zero, W, C], ![W, .literal .zero, C], ![A, .literal .zero, U],
    ![A, U, .literal .zero], ![V, D, .literal .zero], ![.literal .zero, D, V]]

theorem power_source (e : Expr) (n : ℕ) : (power e n).rational = e.rational.power n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [power, Syntax.rational, RationalExpression.power, ih]

theorem chosen_source (slot : Fin 9) : (chosen slot).rational = RationalThreeGeometryCode.chosen slot := by
  fin_cases slot <;> rfl

theorem vertex_source (i : Fin 6) (j : Fin 3) : (vertex i j).rational = RationalThreeGeometryCode.vertex i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem chosen_interpreted (slot : Fin 9) : (chosen slot).compile.interpreted = RationalThreeGeometryCode.chosen slot :=
  (chosen slot).compile_interpreted.trans (chosen_source slot)
theorem vertex_interpreted (i : Fin 6) (j : Fin 3) : (vertex i j).compile.interpreted = RationalThreeGeometryCode.vertex i j :=
  (vertex i j).compile_interpreted.trans (vertex_source i j)

theorem compiled_sizes : (∀ slot, (chosen slot).compileAllocated ≤ 1536 ∧
    (chosen slot).compile.syntaxNodes ≤ 256 ∧ (chosen slot).compile.literalCount ≤ 256) ∧
    (∀ i j, (vertex i j).compileAllocated ≤ 48 ∧ (vertex i j).compile.syntaxNodes ≤ 8 ∧
      (vertex i j).compile.literalCount ≤ 8) := by
  constructor
  · intro slot; fin_cases slot <;> decide
  · intro i j; fin_cases i <;> fin_cases j <;> decide

def descriptor (env : FixedArrayTable 4 SignedWord) : BinaryStoredOverlapEnvironment.Segment 3 9 where
  weight := FixedArrayTable.ofFn (fun slot => ((chosen slot).compile.run env).1)
  P := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j =>
    ((vertex (RationalThreeGeometry.edges slot).1 j).compile.run env).1))
  Q := FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j =>
    ((vertex (RationalThreeGeometry.edges slot).2 j).compile.run env).1))

theorem descriptor_canonical (env : FixedArrayTable 4 SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) : (descriptor env).Canonical := by
  constructor
  · intro slot
    simp only [descriptor, FixedArrayTable.read_ofFn]
    exact (chosen slot).compile.run_canonical env hEnv (chosen slot).compile_canonical
  · constructor
    · intro slot j
      simp only [descriptor, FixedArrayTable.read_ofFn]
      exact (vertex _ j).compile.run_canonical env hEnv (vertex _ j).compile_canonical
    · intro slot j
      simp only [descriptor, FixedArrayTable.read_ofFn]
      exact (vertex _ j).compile.run_canonical env hEnv (vertex _ j).compile_canonical

theorem descriptor_refines (env : FixedArrayTable 4 SignedWord) (g : RationalThreeGeometry)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j))
    (hInputs : BinaryRationalExpression.interpretedEnvironment env = RationalThreeGeometryCode.environment g) :
    (descriptor env).Refines (RationalThreeGeometryCode.compiledLottery g) := by
  rw [RationalThreeGeometryCode.compiledLottery_eq]
  constructor
  · intro slot
    simp only [descriptor, FixedArrayTable.read_ofFn]
    have he := (chosen slot).compile_run_value env hEnv
    rw [chosen_source, hInputs] at he
    exact he.trans (RationalThreeGeometryCode.chosen_value g slot)
  · constructor
    · intro slot j
      simp only [descriptor, FixedArrayTable.read_ofFn]
      have he := (vertex (RationalThreeGeometry.edges slot).1 j).compile_run_value env hEnv
      rw [vertex_source, hInputs] at he
      exact he.trans (RationalThreeGeometryCode.vertex_value g _ j)
    · intro slot j
      simp only [descriptor, FixedArrayTable.read_ofFn]
      have he := (vertex (RationalThreeGeometry.edges slot).2 j).compile_run_value env hEnv
      rw [vertex_source, hInputs] at he
      exact he.trans (RationalThreeGeometryCode.vertex_value g _ j)

def descriptorWork (env : FixedArrayTable 4 SignedWord) : ℕ :=
  (∑ slot : Fin 9, (chosen slot).compile.bitWork env) +
    (∑ slot : Fin 9, ∑ j : Fin 3, (vertex (RationalThreeGeometry.edges slot).1 j).compile.bitWork env) +
    (∑ slot : Fin 9, ∑ j : Fin 3, (vertex (RationalThreeGeometry.edges slot).2 j).compile.bitWork env) + 25000

def descriptorWithWork (env : FixedArrayTable 4 SignedWord) : BinaryStoredOverlapEnvironment.Segment 3 9 × ℕ :=
  (descriptor env, descriptorWork env)

theorem descriptorWork_bound (env : FixedArrayTable 4 SignedWord) (g : RationalThreeGeometry)
    (hEnv : ∀ j, CanonicalWord (env.read j))
    (hInputs : BinaryRationalExpression.interpretedEnvironment env = RationalThreeGeometryCode.environment g)
    (s : ℕ) (hs : 2 ≤ s) (hHeight : ∀ j, RationalHeight ((RationalThreeGeometryCode.environment g).read j) s) :
    descriptorWork env ≤ 2304 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) +
      432 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) + 25000 := by
  have hc : ∀ slot, (chosen slot).compile.bitWork env ≤ 256 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) := by
    intro slot
    have he := (chosen slot).compile.bitWork_bound env hEnv (chosen slot).compile_canonical
      (expressionHeightBudget s 16) (by rw [chosen_interpreted, hInputs]; exact RationalThreeGeometryCode.chosen_intermediates g slot s hs hHeight)
    rw [chosen_interpreted] at he
    exact he.trans (Nat.mul_le_mul_right _ (RationalThreeGeometryCode.chosen_operationBound slot))
  have hv : ∀ i j, (vertex i j).compile.bitWork env ≤ 8 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) := by
    intro i j
    have he := (vertex i j).compile.bitWork_bound env hEnv (vertex i j).compile_canonical
      (expressionHeightBudget s 2) (by rw [vertex_interpreted, hInputs]; exact RationalThreeGeometryCode.vertex_intermediates g i j s hs hHeight)
    rw [vertex_interpreted] at he
    exact he.trans (Nat.mul_le_mul_right _ (RationalThreeGeometryCode.vertex_operationBound i j))
  have hcSum : (∑ slot : Fin 9, (chosen slot).compile.bitWork env) ≤ 2304 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) :=
    (Finset.sum_le_sum (fun slot _ => hc slot)).trans_eq (by simp; ring)
  have hpSum : (∑ slot : Fin 9, ∑ j : Fin 3, (vertex (RationalThreeGeometry.edges slot).1 j).compile.bitWork env) ≤
      216 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) :=
    (Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hv _ j))).trans_eq (by simp; ring)
  have hqSum : (∑ slot : Fin 9, ∑ j : Fin 3, (vertex (RationalThreeGeometry.edges slot).2 j).compile.bitWork env) ≤
      216 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) :=
    (Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hv _ j))).trans_eq (by simp; ring)
  unfold descriptorWork
  omega

theorem descriptor_primitive_workspace (env : FixedArrayTable 4 SignedWord) (g : RationalThreeGeometry)
    (hEnv : ∀ j, CanonicalWord (env.read j))
    (hInputs : BinaryRationalExpression.interpretedEnvironment env = RationalThreeGeometryCode.environment g)
    (s : ℕ) (hs : 2 ≤ s) (hHeight : ∀ j, RationalHeight ((RationalThreeGeometryCode.environment g).read j) s) :
    (∀ slot, (chosen slot).compile.primitiveWorkspace env ≤ 256 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 16)) ∧
      (∀ i j, (vertex i j).compile.primitiveWorkspace env ≤ 8 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 2)) := by
  constructor
  · intro slot
    have he := (chosen slot).compile.primitiveWorkspace_bound env hEnv (chosen slot).compile_canonical
      (expressionHeightBudget s 16) (by rw [chosen_interpreted, hInputs]; exact RationalThreeGeometryCode.chosen_intermediates g slot s hs hHeight)
    rw [chosen_interpreted] at he
    exact he.trans (Nat.mul_le_mul_right _ (RationalThreeGeometryCode.chosen_operationBound slot))
  · intro i j
    have he := (vertex i j).compile.primitiveWorkspace_bound env hEnv (vertex i j).compile_canonical
      (expressionHeightBudget s 2) (by rw [vertex_interpreted, hInputs]; exact RationalThreeGeometryCode.vertex_intermediates g i j s hs hHeight)
    rw [vertex_interpreted] at he
    exact he.trans (Nat.mul_le_mul_right _ (RationalThreeGeometryCode.vertex_operationBound i j))

def chosenStorageBound (s : ℕ) : ℕ :=
  4 * (4 * expressionHeightBudget s 16 + 3) + 307 * (8 * expressionHeightBudget s 16 + 7) +
    4 * 274 + 256 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 16)

def vertexStorageBound (s : ℕ) : ℕ :=
  4 * (4 * expressionHeightBudget s 2 + 3) + 17 * (8 * expressionHeightBudget s 2 + 7) +
    4 * 12 + 8 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 2)

theorem descriptor_evaluation_storage (env : FixedArrayTable 4 SignedWord) (g : RationalThreeGeometry)
    (hEnv : ∀ j, CanonicalWord (env.read j))
    (hInputs : BinaryRationalExpression.interpretedEnvironment env = RationalThreeGeometryCode.environment g)
    (s : ℕ) (hs : 2 ≤ s) (hHeight : ∀ j, RationalHeight ((RationalThreeGeometryCode.environment g).read j) s) :
    (∀ slot, (chosen slot).compile.evaluationStorageWithWorkspace env ≤ chosenStorageBound s) ∧
      (∀ i j, (vertex i j).compile.evaluationStorageWithWorkspace env ≤ vertexStorageBound s) := by
  have hEnvHeight : ∀ j, RationalHeight (value (env.read j)) s := by
    intro j
    have he := hHeight j
    rw [← hInputs] at he
    simpa only [BinaryRationalExpression.interpretedEnvironment, FixedArrayTable.read_ofFn] using he
  constructor
  · intro slot
    have hh : ∀ j, RationalHeight (value (env.read j)) (expressionHeightBudget s 16) := fun j =>
      (hEnvHeight j).mono (expressionHeightBudget_ge_input s 16)
    have he := (chosen slot).compile.evaluationStorageWithWorkspace_bound env hEnv (chosen slot).compile_canonical
      (expressionHeightBudget s 16) (by rw [chosen_interpreted, hInputs]; exact RationalThreeGeometryCode.chosen_intermediates g slot s hs hHeight) hh
    rw [(chosen slot).compile.depth_interpreted, chosen_interpreted] at he
    have hd := RationalThreeGeometryCode.chosen_depth slot
    have hn := (compiled_sizes.1 slot).2.1
    have hl := (compiled_sizes.1 slot).2.2
    have ho := RationalThreeGeometryCode.chosen_operationBound slot
    have hTerm : (chosen slot).compile.literalCount + 3 * ((RationalThreeGeometryCode.chosen slot).depth + 1) ≤ 307 := by omega
    have hControl : (RationalThreeGeometryCode.chosen slot).depth + (chosen slot).compile.syntaxNodes + 2 ≤ 274 := by omega
    unfold chosenStorageBound
    exact he.trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right _ hTerm) _)
      (Nat.mul_le_mul_left 4 hControl)) (Nat.mul_le_mul_right _ ho))
  · intro i j
    have hh : ∀ j, RationalHeight (value (env.read j)) (expressionHeightBudget s 2) := fun j =>
      (hEnvHeight j).mono (expressionHeightBudget_ge_input s 2)
    have he := (vertex i j).compile.evaluationStorageWithWorkspace_bound env hEnv (vertex i j).compile_canonical
      (expressionHeightBudget s 2) (by rw [vertex_interpreted, hInputs]; exact RationalThreeGeometryCode.vertex_intermediates g i j s hs hHeight) hh
    rw [(vertex i j).compile.depth_interpreted, vertex_interpreted] at he
    have hd := RationalThreeGeometryCode.vertex_depth i j
    have hn := (compiled_sizes.2 i j).2.1
    have hl := (compiled_sizes.2 i j).2.2
    have ho := RationalThreeGeometryCode.vertex_operationBound i j
    have hTerm : (vertex i j).compile.literalCount + 3 * ((RationalThreeGeometryCode.vertex i j).depth + 1) ≤ 17 := by omega
    have hControl : (RationalThreeGeometryCode.vertex i j).depth + (vertex i j).compile.syntaxNodes + 2 ≤ 12 := by omega
    unfold vertexStorageBound
    exact he.trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right _ hTerm) _)
      (Nat.mul_le_mul_left 4 hControl)) (Nat.mul_le_mul_right _ ho))

end Blotto.BinaryThreeDescriptorCompiler
