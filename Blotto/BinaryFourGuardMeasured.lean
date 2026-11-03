import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryQuadraticExpressionMeasured
import Blotto.BinaryFourGuardLifetime

/-! The reached ordered-four branch guard consumes measured subtraction,
multiplication and comparison once, retaining the full old Boolean/trace.
Original canonical six-field heights derive its source price; native observer,
reference and allocator realization remains separate. -/

namespace Blotto.BinaryFourGuardMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFactoryHeight BinaryExpressionCompiler
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 3500000

def guardWithExtras (input : BinaryFourParameters.Input) : ((Bool × Trace) × ℕ) × ℕ :=
  let first := BinaryNormalizedCoordinate.opcode .sub Constant.one.word input.p
  let complement := first.1
  let second := BinaryNormalizedCoordinate.opcode .mul complement.1.1 input.ell
  let threshold := second.1
  let compared := BinaryQuadraticExpressionMeasured.compare threshold.1.1 input.w
  (((compared.1.1,wrap 32 2 [complement.1.2,threshold.1.2,compared.1.2]),complement.2+threshold.2+compared.2+8),first.2+second.2)

def guard (input : BinaryFourParameters.Input) : (Bool × Trace) × ℕ :=
  (guardWithExtras input).1

theorem guardWithExtras_compat (input : BinaryFourParameters.Input) :
    (guardWithExtras input).1 = guard input := rfl

theorem guard_record (input : BinaryFourParameters.Input) :
    guard input =
  let complement := BinaryPlannedQuadratic.apply .sub Constant.one.word input.p
  let threshold := BinaryPlannedQuadratic.apply .mul complement.1.1 input.ell
  let compared := BinaryQuadraticExpressionMeasured.compare threshold.1.1 input.w
  ((compared.1.1,wrap 32 2 [complement.1.2,threshold.1.2,compared.1.2]),complement.2+threshold.2+compared.2+8) := by
  simp only [guard,guardWithExtras,BinaryNormalizedCoordinate.opcode_record]

theorem guard_erases (input : BinaryFourParameters.Input) :
    (guard input).1 = BinaryFourGuardLifetime.guardWithTrace input := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,guard_record,BinaryFourGuardLifetime.guardWithTrace,BinaryQuadraticMeasured.apply_erases,
    BinaryQuadraticExpressionMeasured.compare_erases]

def workEnvelope (s : ℕ) : ℕ := 2*11000*(2*expressionHeightBudget s 1+2)^2+
  BinaryQuadraticExpression.uniformPrice (expressionHeightBudget s 2)+8

theorem opcode_work (op : RealArithmeticOp) (a b : SignedWord) (W : ℕ) (ha : width a ≤ W) (hb : width b ≤ W) :
    (BinaryQuadraticMeasured.apply op a b).2 ≤ 11000*(W+1)^2 := by
  have hPair : BinaryRationalArithmetic.pairWidth a b+1 ≤ W+1 := by unfold BinaryRationalArithmetic.pairWidth; omega
  exact (BinaryQuadraticMeasured.apply_bound op a b).trans
    (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left hPair 2))

theorem guard_work (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : BinaryFourNativeOrderWork.InputHeight input s) :
    (guard input).2 ≤ workEnvelope s := by
  let complement := BinaryQuadraticLifetime.applyWithTrace .sub Constant.one.word input.p
  let threshold := BinaryQuadraticLifetime.applyWithTrace .mul complement.1 input.ell
  let compared := BinaryQuadraticExpressionLifetime.compareWithTrace threshold.1 input.w
  have hOneC := Constant.word_canonical .one
  have hOne := one_height s hs
  have hP : CanonicalWord input.p := hC.2.2.2.2.2
  have hEll : CanonicalWord input.ell := hC.2.2.2.2.1
  have hCompState : complement.1 = BinaryRationalOpcode.apply .sub Constant.one.word input.p :=
    BinaryQuadraticLifetime.applyWithTrace_state .sub _ _ hOneC.1 hP.1
  have hCompC : CanonicalWord complement.1 := by
    rw [hCompState]
    exact BinaryReflectedFourSetup.opcode_canonical .sub _ _ hOneC hP
  have hCompHeight : RationalHeight (value complement.1) (expressionHeightBudget s 1) := by
    rw [hCompState,BinaryRationalOpcode.apply_value .sub _ _ hOneC.1 hP.1]
    have h1 : RationalHeight (value Constant.one.word) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hOne
    have h2 : RationalHeight (value input.p) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hHeight.2.2.2.2.2
    exact h1.sub_level h2
  have hThresholdState : threshold.1 = BinaryRationalOpcode.apply .mul complement.1 input.ell :=
    BinaryQuadraticLifetime.applyWithTrace_state .mul _ _ hCompC.1 hEll.1
  have hThresholdC : CanonicalWord threshold.1 := by
    rw [hThresholdState]
    exact BinaryReflectedFourSetup.opcode_canonical .mul _ _ hCompC hEll
  have hThresholdHeight : RationalHeight (value threshold.1) (expressionHeightBudget s 2) := by
    rw [hThresholdState,BinaryRationalOpcode.apply_value .mul _ _ hCompC.1 hEll.1]
    exact hCompHeight.mul_level (hHeight.2.2.2.2.1.mono (expressionHeightBudget_ge_input s 1))
  have hBase : 2 * s + 1 ≤ 2 * expressionHeightBudget s 1 + 1 := by
    have he := expressionHeightBudget_ge_input s 1
    omega
  have hOneW : width Constant.one.word ≤ 2 * expressionHeightBudget s 1 + 1 := by
    have h := hOneC.2.trans (rationalWordWidth_of_height hOne)
    omega
  have hPW : width input.p ≤ 2 * expressionHeightBudget s 1 + 1 := by
    have h := hP.2.trans (rationalWordWidth_of_height hHeight.2.2.2.2.2)
    omega
  have hEllW : width input.ell ≤ 2 * expressionHeightBudget s 1 + 1 := by
    have h := hEll.2.trans (rationalWordWidth_of_height hHeight.2.2.2.2.1)
    omega
  have hCompW : width complement.1 ≤ 2 * expressionHeightBudget s 1 + 1 := by
    have h := hCompC.2.trans (rationalWordWidth_of_height hCompHeight)
    omega
  have hThresholdW : width threshold.1 ≤ 2 * expressionHeightBudget s 2 + 1 := by
    have h := hThresholdC.2.trans (rationalWordWidth_of_height hThresholdHeight)
    omega
  have hW : width input.w ≤ 2 * expressionHeightBudget s 2 + 1 := by
    have h := hC.2.2.2.1.2.trans (rationalWordWidth_of_height hHeight.2.2.2.1)
    have he := expressionHeightBudget_ge_input s 2
    omega
  have hSub := opcode_work .sub Constant.one.word input.p (2*expressionHeightBudget s 1+1) hOneW hPW
  have hMul := opcode_work .mul complement.1 input.ell (2*expressionHeightBudget s 1+1) hCompW hEllW
  have hCompare : (BinaryQuadraticExpressionMeasured.compare threshold.1 input.w).2 ≤
      BinaryQuadraticExpression.uniformPrice (expressionHeightBudget s 2) := by
    rw [BinaryQuadraticExpressionMeasured.compare_work]
    exact BinaryQuadraticExpression.comparePrice_bound _ _ _ (by omega) (by omega)
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,guard_record,BinaryQuadraticMeasured.apply_erases]
  change (BinaryQuadraticMeasured.apply .sub Constant.one.word input.p).2+
    (BinaryQuadraticMeasured.apply .mul complement.1 input.ell).2+
    (BinaryQuadraticExpressionMeasured.compare threshold.1 input.w).2+8 ≤ _
  have hBase : 2*expressionHeightBudget s 1+1+1 = 2*expressionHeightBudget s 1+2 := by omega
  rw [hBase] at hSub hMul
  unfold workEnvelope
  nlinarith only [hSub,hMul,hCompare]

theorem guard_correct (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (guard input).1.1 = BinaryFourParentCompiler.gluingCase input := by
  rw [guard_erases]
  exact BinaryFourGuardLifetime.guardWithTrace_erasure input hC

theorem all_prefix (input : BinaryFourParameters.Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : BinaryFourNativeOrderWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (guard input).1.2 steps ≤ borrowed+BinaryFourGuardLifetime.envelope s ∧
      framePeak ((guard input).1.2.take steps) ≤ BinaryFourGuardLifetime.envelope s := by
  rw [guard_erases]
  exact BinaryFourGuardLifetime.all_prefix input hC s hs hHeight borrowed steps

end Blotto.BinaryFourGuardMeasured
