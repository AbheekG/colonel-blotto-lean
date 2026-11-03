import Blotto.BinaryThreeFactoryWork
import Blotto.BinaryThreeInputCompiler

/-! Actual ordered three-variable input production has source-independent
arithmetic/guard/descriptor prices and output heights. Both regular geometry
and exceptional endpoints are retained, including total zero division. Copies,
bookkeeping and physical execution remain separate contracts. -/

namespace Blotto.BinaryOrderedThreeFactoryWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler
open BinaryThreeInputCompiler BinaryFactoryHeight BinarySyntaxUniformWork
open scoped BigOperators

def InputHeight (input : Input) (s : ℕ) : Prop :=
  RationalHeight (value input.B) s ∧ RationalHeight (value input.a) s ∧ RationalHeight (value input.d) s ∧
    RationalHeight (value input.c) s ∧ RationalHeight (value input.p) s

theorem environment_height (input : Input) (s : ℕ) (h : InputHeight input s) : EnvHeight input.environment s := by
  intro j
  simp only [Input.environment,FixedArrayTable.read_ofFn]
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

theorem parameter_sizes (j : Fin 4) : (parameters j).rational.depth ≤ 2 ∧ (parameters j).rational.operationBound ≤ 16 := by
  fin_cases j <;> decide

theorem regime_sizes : regime.rational.depth ≤ 2 ∧ regime.rational.operationBound ≤ 8 := by decide

def arithmeticWork (input : Input) : ℕ := regime.compile.bitWork input.environment +
  BinaryRationalArithmetic.lessEqualWork (regime.compile.run input.environment).1 BinaryRationalOpcode.zero +
    if regular input then (∑ j : Fin 4, (parameters j).compile.bitWork input.environment) +
      BinaryThreeDescriptorCompiler.descriptorWork (geometryEnvironment input) else 0

def descriptorWithWork (input : Input) : BinaryStoredOverlapEnvironment.Segment 3 9 × ℕ :=
  (descriptor input,arithmeticWork input)

theorem descriptorWithWork_state (input : Input) : (descriptorWithWork input).1 = descriptor input := rfl

theorem geometry_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (h : InputHeight input s) :
    EnvHeight (geometryEnvironment input) (expressionHeightBudget s 2) := by
  intro j
  rw [geometryEnvironment,FixedArrayTable.read_ofFn]
  exact run_height_bound (parameters j) _ (input_canonical input hC) s 2 hs (environment_height input s h) (parameter_sizes j).1

theorem descriptor_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (h : InputHeight input s) :
    SegmentHeight (descriptor input) (expressionHeightBudget s 18) := by
  have hGeometry := geometry_height input hC s hs h
  have hRegular := BinaryThreeFactoryWork.descriptor_height (geometryEnvironment input) (geometry_canonical input hC)
    _ (height_three hs) hGeometry
  rw [expressionHeightBudget_comp] at hRegular
  unfold descriptor
  split
  · exact hRegular
  · have hm := expressionHeightBudget_ge_input s 18
    have h0 := (zero_height s hs).mono hm
    have h1 := (one_height s hs).mono hm
    refine ⟨?_,?_⟩
    · intro slot
      simp only [exceptional,FixedArrayTable.read_ofFn]
      split <;> assumption
    · intro slot j
      simp only [exceptional,FixedArrayTable.read_ofFn]
      fin_cases j
      · exact ⟨h0,h.2.1.mono hm⟩
      · exact ⟨h0,h.2.2.1.mono hm⟩
      · exact ⟨h.1.mono hm,h0⟩

def bound (s : ℕ) : ℕ := 72 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) +
  compareBound (expressionHeightBudget s 2) + BinaryThreeFactoryWork.bound (expressionHeightBudget s 2)

theorem arithmeticWork_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (h : InputHeight input s) :
    arithmeticWork input ≤ bound s := by
  have hEnv := environment_height input s h
  have hc := input_canonical input hC
  have hRegime := BinarySyntaxUniformWork.bitWork_bound regime input.environment hc s 2 8 hs hEnv regime_sizes.1 regime_sizes.2
  have hRegimeH := run_height_bound regime input.environment hc s 2 hs hEnv regime_sizes.1
  have hRegimeC := regime.compile.run_canonical input.environment hc regime.compile_canonical
  have hGuard := comparator_bound _ BinaryRationalOpcode.zero hRegimeC zero_canonical _ hRegimeH (zero_height _ (height_three hs))
  have hEach := fun j => BinarySyntaxUniformWork.bitWork_bound (parameters j) input.environment hc s 2 16 hs hEnv
    (parameter_sizes j).1 (parameter_sizes j).2
  have hParameters : (∑ j : Fin 4, (parameters j).compile.bitWork input.environment) ≤
      64 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) :=
    (Finset.sum_le_sum (fun j _ => hEach j)).trans_eq (by simp; ring)
  have hDescriptor := BinaryThreeFactoryWork.descriptorWork_bound _ (geometry_canonical input hC) _ (height_three hs)
    (geometry_height input hC s hs h)
  unfold arithmeticWork bound
  split <;> omega

end Blotto.BinaryOrderedThreeFactoryWork
