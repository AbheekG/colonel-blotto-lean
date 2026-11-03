import Blotto.BinaryFourOrderLifetime
import Blotto.BinaryLifetimeUsage

/-! Actual subtraction, multiplication and comparison for the ordered
four-variable gluing guard. Source heights of the six original words derive
both intermediate widths and complete retained allocations/activations. -/
namespace Blotto.BinaryFourGuardLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage BinaryFactoryHeight BinaryExpressionCompiler
set_option maxHeartbeats 2000000

def guardWithTrace (input : BinaryFourParameters.Input) : Bool × Trace :=
  let complement := BinaryQuadraticLifetime.applyWithTrace .sub Constant.one.word input.p
  let threshold := BinaryQuadraticLifetime.applyWithTrace .mul complement.1 input.ell
  let compared := BinaryQuadraticExpressionLifetime.compareWithTrace threshold.1 input.w
  (compared.1,wrap 32 2 [complement.2,threshold.2,compared.2])

theorem guardWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (guardWithTrace input).1 = BinaryFourParentCompiler.gluingCase input := by
  unfold guardWithTrace BinaryFourParentCompiler.gluingCase
  dsimp only
  rw [BinaryQuadraticExpressionLifetime.compareWithTrace_erases,
    BinaryQuadraticLifetime.applyWithTrace_state .sub Constant.one.word input.p
      (Constant.word_canonical .one).1 hC.2.2.2.2.2.1,
    BinaryQuadraticLifetime.applyWithTrace_state .mul _ input.ell
      (BinaryRationalOpcode.apply_valid .sub Constant.one.word input.p
        (Constant.word_canonical .one).1 hC.2.2.2.2.2.1) hC.2.2.2.2.1.1]

def envelope (s : ℕ) : ℕ :=
  2 * opcodeEnvelope (2 * expressionHeightBudget s 1 + 1) +
    BinaryThreeGeometryLifetime.comparisonEnvelope (2 * expressionHeightBudget s 2 + 1) + 48

theorem guardWithTrace_usage (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : BinaryFourNativeOrderWork.InputHeight input s) :
    usage (guardWithTrace input).2 ≤ envelope s := by
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
  have hSub := opcode_usage .sub Constant.one.word input.p (2 * expressionHeightBudget s 1 + 1) hOneW hPW
  have hMul := opcode_usage .mul complement.1 input.ell (2 * expressionHeightBudget s 1 + 1) hCompW hEllW
  have hThresholdW : width threshold.1 ≤ 2 * expressionHeightBudget s 2 + 1 := by
    have h := hThresholdC.2.trans (rationalWordWidth_of_height hThresholdHeight)
    omega
  have hW : width input.w ≤ 2 * expressionHeightBudget s 2 + 1 := by
    have h := hC.2.2.2.1.2.trans (rationalWordWidth_of_height hHeight.2.2.2.1)
    have he := expressionHeightBudget_ge_input s 2
    omega
  have hCompare := BinaryThreeGeometryLifetime.comparison_usage threshold.1 input.w
    (2 * expressionHeightBudget s 2 + 1) hThresholdW hW
  change usage complement.2 ≤ _ at hSub
  change usage threshold.2 ≤ _ at hMul
  change usage compared.2 ≤ _ at hCompare
  have hw := wrap_usage 32 2 [complement.2,threshold.2,compared.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [complement.2,threshold.2,compared.2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (input : BinaryFourParameters.Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : BinaryFourNativeOrderWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (guardWithTrace input).2 steps ≤ borrowed + envelope s ∧
      framePeak ((guardWithTrace input).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (guardWithTrace_usage input hC s hs hHeight) borrowed steps

end Blotto.BinaryFourGuardLifetime
