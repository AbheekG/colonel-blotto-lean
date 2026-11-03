import Blotto.BinarySyntaxUniformWork
import Blotto.BinaryNestedParameters

/-! Actual nested parameter and geometry producers have checked finite syntax
depth/count envelopes and source-independent stored-word height/primitive prices.
This includes total zero division and every branch. Environment/table metadata,
bookkeeping and physical execution remain separate. -/

namespace Blotto.BinaryNestedParameterWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryNestedParameters
open BinarySyntaxUniformWork
open scoped BigOperators

def InputHeight (input : Input) (s : ℕ) : Prop :=
  RationalHeight (value input.M) s ∧ RationalHeight (value input.a) s ∧ RationalHeight (value input.d) s ∧
    RationalHeight (value input.c) s ∧ RationalHeight (value input.t) s ∧ RationalHeight (value input.q) s

theorem environment_height (input : Input) (x : SignedWord) (s : ℕ) (h : InputHeight input s)
    (hx : RationalHeight (value x) s) : EnvHeight (environment input x) s := by
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

theorem program_sizes (j : Fin 9) : (programs j).rational.depth ≤ 16 ∧ (programs j).rational.operationBound ≤ 256 := by
  fin_cases j <;> decide

theorem geometry_sizes (j : Fin 4) : (firstParameters j).rational.depth ≤ 16 ∧
    (firstParameters j).rational.operationBound ≤ 256 := by fin_cases j <;> decide

def prepareWork (input : Input) (x : SignedWord) : ℕ := ∑ j : Fin 9, (programs j).compile.bitWork (environment input x)
def geometryWork (input : Input) (x : SignedWord) : ℕ := ∑ j : Fin 4, (firstParameters j).compile.bitWork (environment input x)

def prepareWithWork (input : Input) (x : SignedWord) : FixedArrayTable 9 SignedWord × ℕ :=
  (prepare input x,prepareWork input x)

theorem prepareWithWork_state (input : Input) (x : SignedWord) : (prepareWithWork input x).1 = prepare input x := rfl

theorem prepare_height (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) (hXH : RationalHeight (value x) s) (j : Fin 9) :
    RationalHeight (value ((prepare input x).read j)) (expressionHeightBudget s 16) := by
  rw [prepare,FixedArrayTable.read_ofFn]
  exact run_height_bound _ _ (environment_canonical input x hC hX) s 16 hs (environment_height input x s hH hXH) (program_sizes j).1

theorem geometry_height (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) (hXH : RationalHeight (value x) s) (j : Fin 4) :
    RationalHeight (value ((geometry input x).read j)) (expressionHeightBudget s 16) := by
  rw [geometry,FixedArrayTable.read_ofFn]
  exact run_height_bound _ _ (environment_canonical input x hC hX) s 16 hs (environment_height input x s hH hXH) (geometry_sizes j).1

theorem prepareWork_bound (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) (hXH : RationalHeight (value x) s) :
    prepareWork input x ≤ 2304 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) := by
  have hEach := fun j => BinarySyntaxUniformWork.bitWork_bound (programs j) (environment input x)
    (environment_canonical input x hC hX) s 16 256 hs (environment_height input x s hH hXH)
    (program_sizes j).1 (program_sizes j).2
  exact (Finset.sum_le_sum (fun j _ => hEach j)).trans_eq (by simp; ring)

theorem geometryWork_bound (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) (hXH : RationalHeight (value x) s) :
    geometryWork input x ≤ 1024 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) := by
  have hEach := fun j => BinarySyntaxUniformWork.bitWork_bound (firstParameters j) (environment input x)
    (environment_canonical input x hC hX) s 16 256 hs (environment_height input x s hH hXH)
    (geometry_sizes j).1 (geometry_sizes j).2
  exact (Finset.sum_le_sum (fun j _ => hEach j)).trans_eq (by simp; ring)

end Blotto.BinaryNestedParameterWork
