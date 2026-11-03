import Blotto.BinaryOrderedThreeFactoryWork
import Blotto.BinaryNestedFamilyFactoryWork

/-! Native translated-uniform and residual component factories retain their
actual parameter/subtraction/descriptor data and exact old tables. Finite AST
and original-field heights derive primitive prices, including zero division.
Profile branch composition and complete model costs remain separate. -/

namespace Blotto.BinaryNestedRemainingFactoryWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryExpressionCompiler
open BinaryNestedParameters BinaryNestedComponents BinaryNestedParameterWork BinaryFactoryHeight BinarySyntaxUniformWork
open scoped BigOperators

theorem mirror_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) :
    RationalHeight (value (mirror input)) (expressionHeightBudget s 16) :=
  prepare_height input zero hC zero_canonical s hs hH (zero_height s hs) 6

theorem second_input_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) :
    BinaryOrderedThreeFactoryWork.InputHeight (secondUniformInput input) (expressionHeightBudget s 17) := by
  have hMirror := mirror_height input hC s hs hH
  have hm16 := expressionHeightBudget_ge_input s 16
  have hm17 := expressionHeightBudget_ge_input s 17
  have hFirst : RationalHeight (value (apply .sub input.M (mirror input))) (expressionHeightBudget s 17) := by
    rw [apply_value .sub _ _ hC.1.1 (mirror_canonical input hC).1]
    have h := ((hH.1.mono hm16).sub_level hMirror)
    exact h
  have hThird : RationalHeight (value (apply .sub input.t (mirror input))) (expressionHeightBudget s 17) := by
    rw [apply_value .sub _ _ hC.2.2.2.2.1.1 (mirror_canonical input hC).1]
    exact (hH.2.2.2.2.1.mono hm16).sub_level hMirror
  exact ⟨hFirst,hH.2.1.mono hm17,hH.2.2.1.mono hm17,hThird,one_height _ (height_three hs)⟩

def secondWithWork (input : Input) : BinaryStoredOverlapEnvironment.Segment 3 9 × ℕ :=
  let parameters := BinaryNestedParameterWork.prepareWithWork input zero
  let mirror := parameters.1.read 6
  let budget := applyWithWork .sub input.M mirror
  let length := applyWithWork .sub input.t mirror
  let child : BinaryThreeInputCompiler.Input := ⟨budget.1,input.a,input.d,length.1,Constant.one.word⟩
  let table := BinaryOrderedThreeFactoryWork.descriptorWithWork child
  (BinarySegmentAssembly.shiftThird table.1 mirror,parameters.2 + budget.2 + length.2 + table.2 +
    BinaryAssemblyArithmeticWork.shiftWork table.1 mirror)

theorem secondWithWork_state (input : Input) : (secondWithWork input).1 = secondUniformLottery input := by
  unfold secondWithWork secondUniformLottery secondUniformInput BinaryNestedComponents.mirror
  simp only [BinaryNestedParameterWork.prepareWithWork_state,applyWithWork_state,BinaryOrderedThreeFactoryWork.descriptorWithWork_state]

def secondBound (s : ℕ) : ℕ := 2304 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) +
  2 * opcodeBound (expressionHeightBudget s 16) + BinaryOrderedThreeFactoryWork.bound (expressionHeightBudget s 17) +
    18 * opcodeBound (expressionHeightBudget s 35)

theorem second_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) :
    SegmentHeight (secondUniformLottery input) (expressionHeightBudget s 36) := by
  have hChild := BinaryOrderedThreeFactoryWork.descriptor_height _ (secondUniformInput_canonical input hC)
    _ (height_three hs) (second_input_height input hC s hs hH)
  rw [expressionHeightBudget_comp] at hChild
  have hm := (mirror_height input hC s hs hH).mono (expressionHeightBudget_mono s (by decide : 16 ≤ 35))
  have h := BinaryAssemblyArithmeticWork.shift_height _ _ (BinaryThreeInputCompiler.descriptor_canonical _ (secondUniformInput_canonical input hC))
    (mirror_canonical input hC) _ hChild hm
  rw [expressionHeightBudget_comp] at h
  exact h

theorem secondWithWork_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) :
    (secondWithWork input).2 ≤ secondBound s := by
  have hP := prepareWork_bound input zero hC zero_canonical s hs hH (zero_height s hs)
  have hMirror := mirror_height input hC s hs hH
  have hm := expressionHeightBudget_ge_input s 16
  have hB := opcode_bound .sub input.M (mirror input) hC.1 (mirror_canonical input hC) _ (hH.1.mono hm) hMirror
  have hL := opcode_bound .sub input.t (mirror input) hC.2.2.2.2.1 (mirror_canonical input hC) _ (hH.2.2.2.2.1.mono hm) hMirror
  have hCChild := secondUniformInput_canonical input hC
  have hHeight := second_input_height input hC s hs hH
  have hTableWork := BinaryOrderedThreeFactoryWork.arithmeticWork_bound _ hCChild _ (height_three hs) hHeight
  have hTable := BinaryOrderedThreeFactoryWork.descriptor_height _ hCChild _ (height_three hs) hHeight
  rw [expressionHeightBudget_comp] at hTable
  have hShift := BinaryAssemblyArithmeticWork.shiftWork_bound _ (mirror input) (BinaryThreeInputCompiler.descriptor_canonical _ hCChild)
    (mirror_canonical input hC) _ hTable (hMirror.mono (expressionHeightBudget_mono s (by decide : 16 ≤ 35)))
  unfold secondWithWork
  simp only [BinaryNestedParameterWork.prepareWithWork_state,applyWithWork_state,BinaryOrderedThreeFactoryWork.descriptorWithWork_state]
  change prepareWork input zero + (applyWithWork .sub input.M (mirror input)).2 +
    (applyWithWork .sub input.t (mirror input)).2 + BinaryOrderedThreeFactoryWork.arithmeticWork (secondUniformInput input) +
    BinaryAssemblyArithmeticWork.shiftWork (BinaryThreeInputCompiler.descriptor (secondUniformInput input)) (mirror input) ≤ _
  unfold secondBound
  nlinarith

theorem residual_sizes (slot : Fin 3) : (BinaryNestedResidualCompiler.weights slot).rational.depth ≤ 8 ∧
    (BinaryNestedResidualCompiler.weights slot).rational.operationBound ≤ 128 := by fin_cases slot <;> decide

theorem residual_vertex_sizes (slot : Fin 3) (j : Fin 3) : (BinaryNestedResidualCompiler.vertices slot j).rational.depth ≤ 8 ∧
    (BinaryNestedResidualCompiler.vertices slot j).rational.operationBound ≤ 128 := by fin_cases slot <;> fin_cases j <;> decide

theorem residual_env_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) :
    EnvHeight (residualEnvironment input) (expressionHeightBudget s 16) := by
  have hp := prepare_height input zero hC zero_canonical s hs hH (zero_height s hs)
  have hm := expressionHeightBudget_ge_input s 16
  intro j
  simp only [residualEnvironment,FixedArrayTable.read_ofFn]
  fin_cases j
  · exact hp 1
  · exact hp 2
  · change RationalHeight (value (apply .sub input.M input.c)) _
    rw [apply_value .sub _ _ hC.1.1 hC.2.2.2.1.1]
    have ha : RationalHeight (value input.M) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hH.1
    have hb : RationalHeight (value input.c) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hH.2.2.2.1
    exact (ha.sub_level hb).mono (expressionHeightBudget_mono s (by decide : 1 ≤ 16))
  · exact hp 0
  · exact hH.2.2.2.2.1.mono hm

def residualWithWork (input : Input) : BinaryStoredOverlapEnvironment.Segment 3 3 × ℕ :=
  let parameters := BinaryNestedParameterWork.prepareWithWork input zero
  let difference := applyWithWork .sub input.M input.c
  let env := FixedArrayTable.ofFn ![parameters.1.read 1,parameters.1.read 2,difference.1,parameters.1.read 0,input.t]
  let table := BinaryNestedResidualCompiler.descriptorWithWork env
  (table.1,parameters.2 + difference.2 + table.2)

theorem residualWithWork_state (input : Input) : (residualWithWork input).1 = residualLottery input := by
  unfold residualWithWork residualLottery residualEnvironment
  simp only [BinaryNestedParameterWork.prepareWithWork_state,applyWithWork_state,BinaryNestedResidualCompiler.descriptorWithWork_state]

theorem residual_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) :
    SegmentHeight (residualLottery input) (expressionHeightBudget s 24) := by
  have he := residual_env_height input hC s hs hH
  have hc := residualEnvironment_canonical input hC
  refine ⟨?_,?_⟩
  · intro slot
    rw [residualLottery,BinaryNestedResidualCompiler.descriptor,FixedArrayTable.read_ofFn]
    have h := run_height_bound _ _ hc _ 8 (height_three hs) he (residual_sizes slot).1
    rw [expressionHeightBudget_comp] at h
    exact h
  · intro slot j
    constructor
    · rw [residualLottery,BinaryNestedResidualCompiler.descriptor,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
      have h := run_height_bound (BinaryNestedResidualCompiler.vertices (RationalNestedResidual.edges slot).1 j) _ hc _ 8 (height_three hs) he (residual_vertex_sizes (RationalNestedResidual.edges slot).1 j).1
      rw [expressionHeightBudget_comp] at h
      exact h
    · rw [residualLottery,BinaryNestedResidualCompiler.descriptor,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
      have h := run_height_bound (BinaryNestedResidualCompiler.vertices (RationalNestedResidual.edges slot).2 j) _ hc _ 8 (height_three hs) he (residual_vertex_sizes (RationalNestedResidual.edges slot).2 j).1
      rw [expressionHeightBudget_comp] at h
      exact h

def residualBound (s : ℕ) : ℕ := 2304 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 16) +
  opcodeBound s + 2688 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 24) + 1000

theorem residualWithWork_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (hH : InputHeight input s) :
    (residualWithWork input).2 ≤ residualBound s := by
  have hP := prepareWork_bound input zero hC zero_canonical s hs hH (zero_height s hs)
  have hD := opcode_bound .sub input.M input.c hC.1 hC.2.2.2.1 s hH.1 hH.2.2.2.1
  let env := residualEnvironment input
  have he := residual_env_height input hC s hs hH
  have hc := residualEnvironment_canonical input hC
  have hw := fun slot => BinarySyntaxUniformWork.bitWork_bound (BinaryNestedResidualCompiler.weights slot) env hc _ 8 128
    (height_three hs) he (residual_sizes slot).1 (residual_sizes slot).2
  have hv := fun slot j => BinarySyntaxUniformWork.bitWork_bound (BinaryNestedResidualCompiler.vertices slot j) env hc _ 8 128
    (height_three hs) he (residual_vertex_sizes slot j).1 (residual_vertex_sizes slot j).2
  have hW : (∑ slot : Fin 3, (BinaryNestedResidualCompiler.weights slot).compile.bitWork env) ≤
      384 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 24) := by
    have h := (Finset.sum_le_sum (fun slot _ => hw slot)).trans_eq (show (∑ _slot : Fin 3,
      128 * BinaryRationalExpression.uniformPrice (expressionHeightBudget (expressionHeightBudget s 16) 8)) =
        384 * BinaryRationalExpression.uniformPrice (expressionHeightBudget (expressionHeightBudget s 16) 8) by simp; ring)
    simpa only [expressionHeightBudget_comp] using h
  have hV (edge : Fin 3 → Fin 3) : (∑ slot : Fin 3, ∑ j : Fin 3,
      (BinaryNestedResidualCompiler.vertices (edge slot) j).compile.bitWork env) ≤
        1152 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 24) := by
    have h : (∑ slot : Fin 3, ∑ j : Fin 3, (BinaryNestedResidualCompiler.vertices (edge slot) j).compile.bitWork env) ≤
        ∑ _slot : Fin 3, ∑ _j : Fin 3, 128 * BinaryRationalExpression.uniformPrice (expressionHeightBudget (expressionHeightBudget s 16) 8) :=
      Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hv (edge slot) j))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,expressionHeightBudget_comp] at h
    nlinarith
  have hV1 := hV (fun slot => (RationalNestedResidual.edges slot).1)
  have hV2 := hV (fun slot => (RationalNestedResidual.edges slot).2)
  unfold residualWithWork
  simp only [BinaryNestedParameterWork.prepareWithWork_state,applyWithWork_state,BinaryNestedResidualCompiler.descriptorWithWork]
  change prepareWork input zero + (applyWithWork .sub input.M input.c).2 + BinaryNestedResidualCompiler.descriptorWork env ≤ _
  unfold BinaryNestedResidualCompiler.descriptorWork residualBound
  omega

end Blotto.BinaryNestedRemainingFactoryWork
