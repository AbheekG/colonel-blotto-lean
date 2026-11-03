import Blotto.BinaryThreeDescriptorCompiler
import Blotto.RationalThreeInputPreparation

/-! Five stored Boolean words B,a,d,c,p produce the actual three-variable
parent descriptor. The numerical E=a+d-B guard uses the verified Boolean
comparator; positive E builds four geometry parameters and the regular table,
while E≤0 emits the retained exceptional endpoints and weight slot. The input
record's mathematical admissibility/refinement remains explicit proof data;
there is no runtime Rat conversion or supplied geometry environment oracle. -/

namespace Blotto.BinaryThreeInputCompiler
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler

structure Input where
  B : SignedWord
  a : SignedWord
  d : SignedWord
  c : SignedWord
  p : SignedWord

def Input.environment (input : Input) : FixedArrayTable 5 SignedWord :=
  FixedArrayTable.ofFn ![input.B,input.a,input.d,input.c,input.p]

def Input.Canonical (input : Input) : Prop := CanonicalWord input.B ∧ CanonicalWord input.a ∧
  CanonicalWord input.d ∧ CanonicalWord input.c ∧ CanonicalWord input.p

def Input.Refines (input : Input) (source : RationalThreeInput) : Prop :=
  value input.B = source.B ∧ value input.a = source.a ∧ value input.d = source.d ∧
    value input.c = source.c ∧ value input.p = source.p

abbrev Expr := Syntax 5
def B : Expr := .input 0
def A : Expr := .input 1
def D : Expr := .input 2
def C : Expr := .input 3
def P : Expr := .input 4
def regime : Expr := .sub (.add A D) B
def parameters : Fin 4 → Expr := ![.sub B A,.sub B D,.sub B C,.mul C (.sub (.literal .one) P)]

theorem parameters_source (j : Fin 4) : (parameters j).rational = RationalThreeInputCode.parameters j := by fin_cases j <;> rfl
theorem regime_source : regime.rational = RationalThreeInputCode.regime := rfl

theorem input_canonical (input : Input) (h : input.Canonical) : ∀ j, CanonicalWord (input.environment.read j) := by
  intro j
  fin_cases j <;> simp only [Input.environment,FixedArrayTable.read_ofFn]
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

theorem input_environment (input : Input) (source : RationalThreeInput) (h : input.Refines source) :
    BinaryRationalExpression.interpretedEnvironment input.environment = RationalThreeInputCode.environment source := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  rw [BinaryRationalExpression.interpretedEnvironment,FixedArrayTable.read_ofFn]
  unfold Input.environment RationalThreeInputCode.environment
  rw [FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

def geometryEnvironment (input : Input) : FixedArrayTable 4 SignedWord :=
  FixedArrayTable.ofFn (fun j => ((parameters j).compile.run input.environment).1)

theorem geometry_canonical (input : Input) (h : input.Canonical) :
    ∀ j, CanonicalWord ((geometryEnvironment input).read j) := by
  intro j
  rw [geometryEnvironment,FixedArrayTable.read_ofFn]
  exact (parameters j).compile.run_canonical input.environment (input_canonical input h) (parameters j).compile_canonical

theorem geometry_environment (input : Input) (source : RationalThreeInput)
    (hCanonical : input.Canonical) (hRefines : input.Refines source) (hE : 0 < source.a + source.d - source.B) :
    BinaryRationalExpression.interpretedEnvironment (geometryEnvironment input) =
      RationalThreeGeometryCode.environment (source.geometry hE) := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  rw [BinaryRationalExpression.interpretedEnvironment,FixedArrayTable.read_ofFn,
    geometryEnvironment,FixedArrayTable.read_ofFn]
  have he := (parameters j).compile_run_value input.environment (fun r => (input_canonical input hCanonical r).1)
  rw [parameters_source,input_environment input source hRefines] at he
  exact he.trans (RationalThreeInputCode.parameter_value source hE j)

def regular (input : Input) : Bool :=
  !(BinaryRationalArithmetic.lessEqual (regime.compile.run input.environment).1 BinaryRationalOpcode.zero)

theorem regular_iff (input : Input) (source : RationalThreeInput)
    (hCanonical : input.Canonical) (hRefines : input.Refines source) :
    regular input = true ↔ 0 < source.a + source.d - source.B := by
  have hValid := regime.compile.run_valid input.environment (fun r => (input_canonical input hCanonical r).1)
    (regime.compile.canonicalLiterals_valid regime.compile_canonical)
  have hValue := regime.compile_run_value input.environment (fun r => (input_canonical input hCanonical r).1)
  rw [regime_source,input_environment input source hRefines] at hValue
  have hCmp := BinaryRationalArithmetic.lessEqual_iff (regime.compile.run input.environment).1
    BinaryRationalOpcode.zero hValid BinaryRationalOpcode.zero_valid
  rw [hValue,BinaryRationalOpcode.zero_value] at hCmp
  change _ ↔ RationalThreeInputCode.regime.value (RationalThreeInputCode.environment source) ≤ 0 at hCmp
  rw [RationalThreeInputCode.regime_value] at hCmp
  unfold regular
  cases he : BinaryRationalArithmetic.lessEqual (regime.compile.run input.environment).1 BinaryRationalOpcode.zero
  · simp only [Bool.not_false,true_iff]
    have hn : ¬source.a + source.d - source.B ≤ 0 := by intro hh; have h := hCmp.mpr hh; rw [he] at h; cases h
    exact lt_of_not_ge hn
  · simp only [Bool.not_true,Bool.false_eq_true,false_iff]
    exact not_lt.mpr (hCmp.mp he)

def exceptional (input : Input) : BinaryStoredOverlapEnvironment.Segment 3 9 where
  weight := FixedArrayTable.ofFn (fun slot => if slot = 0 then Constant.one.word else Constant.zero.word)
  P := FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![Constant.zero.word,Constant.zero.word,input.B])
  Q := FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![input.a,input.d,Constant.zero.word])

def descriptor (input : Input) : BinaryStoredOverlapEnvironment.Segment 3 9 :=
  if regular input then BinaryThreeDescriptorCompiler.descriptor (geometryEnvironment input) else exceptional input

theorem exceptional_canonical (input : Input) (h : input.Canonical) : (exceptional input).Canonical := by
  constructor
  · intro slot
    simp only [exceptional,FixedArrayTable.read_ofFn]
    split <;> exact Constant.word_canonical _
  · constructor
    · intro slot j
      fin_cases j <;> simp only [exceptional,FixedArrayTable.read_ofFn]
      · exact Constant.word_canonical .zero
      · exact Constant.word_canonical .zero
      · exact h.1
    · intro slot j
      fin_cases j <;> simp only [exceptional,FixedArrayTable.read_ofFn]
      · exact h.2.1
      · exact h.2.2.1
      · exact Constant.word_canonical .zero

theorem descriptor_canonical (input : Input) (h : input.Canonical) : (descriptor input).Canonical := by
  unfold descriptor
  split
  · exact BinaryThreeDescriptorCompiler.descriptor_canonical _ (geometry_canonical input h)
  · exact exceptional_canonical input h

theorem descriptor_refines (input : Input) (source : RationalThreeInput)
    (hCanonical : input.Canonical) (hRefines : input.Refines source) :
    (descriptor input).Refines source.segmentLottery := by
  by_cases hE : 0 < source.a + source.d - source.B
  · have hReg := (regular_iff input source hCanonical hRefines).mpr hE
    unfold descriptor RationalThreeInput.segmentLottery
    rw [ite_eq_left hReg,dite_eq_left hE]
    exact BinaryThreeDescriptorCompiler.descriptor_refines _ _
      (fun j => (geometry_canonical input hCanonical j).1)
      (geometry_environment input source hCanonical hRefines hE)
  · have hReg : ¬regular input = true := fun hp => hE ((regular_iff input source hCanonical hRefines).mp hp)
    unfold descriptor RationalThreeInput.segmentLottery
    rw [ite_eq_right hReg,dite_eq_right hE]
    constructor
    · intro slot
      simp only [exceptional,FixedArrayTable.read_ofFn]
      split <;> exact Constant.word_value _
    · constructor
      · intro slot j
        unfold exceptional
        rw [FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
        fin_cases j
        · exact Constant.word_value .zero

        · exact Constant.word_value .zero
        · exact hRefines.1
      · intro slot j
        unfold exceptional
        rw [FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
        fin_cases j
        · exact hRefines.2.1
        · exact hRefines.2.2.1
        · exact Constant.word_value .zero

def regimeWork (input : Input) : ℕ := regime.compile.bitWork input.environment +
  BinaryRationalArithmetic.lessEqualWork (regime.compile.run input.environment).1 BinaryRationalOpcode.zero + 4

def parameterWork (input : Input) : ℕ :=
  ∑ j : Fin 4, ((parameters j).compile.bitWork input.environment +
    BinaryRationalExpression.payloadWords ((parameters j).compile.run input.environment).1 + 4)

def exceptionalWork (input : Input) : ℕ :=
  9 * (20 + BinaryRationalExpression.payloadWords input.B + BinaryRationalExpression.payloadWords input.a +
    BinaryRationalExpression.payloadWords input.d) + 3

def descriptorWork (input : Input) : ℕ :=
  2 * BinaryRationalExpression.environmentPayload input.environment + 20 + regimeWork input +
    if regular input then parameterWork input + BinaryThreeDescriptorCompiler.descriptorWork (geometryEnvironment input)
    else exceptionalWork input

def descriptorWithWork (input : Input) : BinaryStoredOverlapEnvironment.Segment 3 9 × ℕ :=
  (descriptor input, descriptorWork input)

def workBound (s : ℕ) : ℕ :=
  50 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) +
    2304 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 18) +
    432 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 4) +
    1000 * (s + 1) + 25000

theorem descriptorWork_bound (input : Input) (source : RationalThreeInput)
    (hCanonical : input.Canonical) (hRefines : input.Refines source)
    (s : ℕ) (hs : 2 ≤ s) (hHeight : ∀ j, RationalHeight ((RationalThreeInputCode.environment source).read j) s) :
    descriptorWork input ≤ workBound s := by
  have hc := input_canonical input hCanonical
  have hi := input_environment input source hRefines
  have hH : ∀ j, RationalHeight (value (input.environment.read j)) s := by
    intro j
    have he := hHeight j
    rw [← hi] at he
    simpa only [BinaryRationalExpression.interpretedEnvironment, FixedArrayTable.read_ofFn] using he
  have hRegAll : regime.compile.interpreted.AllRunHeights
      (BinaryRationalExpression.interpretedEnvironment input.environment) (expressionHeightBudget s 2) := by
    rw [regime.compile_interpreted,regime_source,hi]
    exact RationalThreeInputCode.regime_intermediates source s hHeight
  have hRegWork := regime.compile.bitWork_bound input.environment hc regime.compile_canonical _ hRegAll
  have hRegOps : regime.compile.interpreted.operationBound = 5 := by rw [regime.compile_interpreted,regime_source]; rfl
  rw [hRegOps] at hRegWork
  have hRegValue := regime.compile_run_value input.environment (fun j => (hc j).1)
  rw [regime_source,hi] at hRegValue
  have hRegHeight : RationalHeight (value (regime.compile.run input.environment).1) (expressionHeightBudget s 2) := by
    rw [hRegValue]
    exact RationalThreeInputCode.regime_height source s hHeight
  have hRegWidth := regime.compile.run_height_width input.environment hc regime.compile_canonical
    (expressionHeightBudget s 2) (by rw [regime.compile_interpreted,regime_source,hi]; exact RationalThreeInputCode.regime_height source s hHeight)
  have hZeroWidth : width BinaryRationalOpcode.zero ≤ 1 + 2 * expressionHeightBudget s 2 := by change 1 ≤ _; omega
  have hCmp := BinaryRationalExpression.comparePrice_bound (regime.compile.run input.environment).1 BinaryRationalOpcode.zero
    (expressionHeightBudget s 2) hRegWidth hZeroWidth
  have hGuard : regimeWork input ≤ 6 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) := by
    unfold regimeWork BinaryRationalExpression.comparePrice at *
    omega
  have hParameter : parameterWork input ≤ 36 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) := by
    unfold parameterWork
    have hEach : ∀ j : Fin 4, (parameters j).compile.bitWork input.environment +
        BinaryRationalExpression.payloadWords ((parameters j).compile.run input.environment).1 + 4 ≤
        9 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) := by
      intro j
      have hL := (RationalThreeInputCode.parameters j).LiteralHeights_mono hs (RationalThreeInputCode.parameter_literals j)
      have hAll := (RationalThreeInputCode.parameters j).run_all_heights _ s hHeight hL
      have hAll' := RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s (RationalThreeInputCode.parameter_depth j)) hAll
      have hw := (parameters j).compile.bitWork_bound input.environment hc (parameters j).compile_canonical _
        (by rw [(parameters j).compile_interpreted,parameters_source,hi]; exact hAll')
      rw [(parameters j).compile_interpreted,parameters_source] at hw
      have ho := RationalThreeInputCode.parameter_operations j
      have hWord := (parameters j).compile.run_canonical input.environment hc (parameters j).compile_canonical
      have hValue := (parameters j).compile_run_value input.environment (fun r => (hc r).1)
      rw [parameters_source,hi] at hValue
      have hv := ((RationalThreeInputCode.parameters j).run_height _ s hHeight hL).mono
        (expressionHeightBudget_mono s (RationalThreeInputCode.parameter_depth j))
      rw [← hValue] at hv
      have hWidth := hWord.2.trans (rationalWordWidth_of_height hv)
      have hp := BinaryRationalExpression.payloadWords_bound ((parameters j).compile.run input.environment).1 _ hWidth
      have hPrice : 4 * expressionHeightBudget s 2 + 7 ≤ BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) := by
        unfold BinaryRationalExpression.uniformPrice
        have he : 2 * expressionHeightBudget s 2 + 2 ≤ (2 * expressionHeightBudget s 2 + 2) ^ 3 := by
          simpa using (Nat.pow_le_pow_right (by omega : 0 < 2 * expressionHeightBudget s 2 + 2) (by omega : 1 ≤ 3))
        omega
      have hw' := hw.trans (Nat.mul_le_mul_right _ ho)
      omega
    calc
      _ ≤ ∑ _j : Fin 4, 9 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 2) :=
        Finset.sum_le_sum (fun j _ => hEach j)
      _ = _ := by simp; ring
  have hEnv := BinaryRationalExpression.environmentPayload_bound input.environment s hc hH
  have hPayload : BinaryRationalExpression.payloadWords input.B ≤ 4*s+3 ∧
      BinaryRationalExpression.payloadWords input.a ≤ 4*s+3 ∧ BinaryRationalExpression.payloadWords input.d ≤ 4*s+3 := by
    have h0 := BinaryRationalExpression.payloadWords_bound input.B _ (hCanonical.1.2.trans (rationalWordWidth_of_height (hH 0)))
    have h1 := BinaryRationalExpression.payloadWords_bound input.a _ (hCanonical.2.1.2.trans (rationalWordWidth_of_height (hH 1)))
    have h2 := BinaryRationalExpression.payloadWords_bound input.d _ (hCanonical.2.2.1.2.trans (rationalWordWidth_of_height (hH 2)))
    exact ⟨by omega,by omega,by omega⟩
  unfold descriptorWork
  split
  · rename_i hReg
    have hE := (regular_iff input source hCanonical hRefines).mp hReg
    have hGeometry := geometry_environment input source hCanonical hRefines hE
    have hDesc := BinaryThreeDescriptorCompiler.descriptorWork_bound (geometryEnvironment input) (source.geometry hE)
      (geometry_canonical input hCanonical) hGeometry (expressionHeightBudget s 2)
      (hs.trans (expressionHeightBudget_ge_input s 2))
      (RationalThreeInputCode.geometry_environment_height source hE s hs hHeight)
    rw [expressionHeightBudget_comp,expressionHeightBudget_comp] at hDesc
    norm_num only [show 2 + 16 = (18 : ℕ) from rfl, show 2 + 2 = (4 : ℕ) from rfl] at hDesc
    unfold workBound
    omega
  · unfold exceptionalWork workBound
    omega

end Blotto.BinaryThreeInputCompiler
