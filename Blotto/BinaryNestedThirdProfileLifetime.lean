import Blotto.BinaryScalarTape
import Blotto.BinaryNestedResidualLifetime

/-! The complete third ordered profile consumes the shared parameters and
actual residual table, then either mixes a family at length v or pads the
residual alone according to the traced positivity guard. -/
namespace Blotto.BinaryNestedThirdProfileLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def profileWithTrace (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (K : ℕ) (bits : BinaryScalarTape K) : Segment × Trace :=
  let residual := BinaryNestedResidualLifetime.residualWithTrace input parameters
  let padded := BinaryNestedResidualLifetime.padWithTrace residual.1
  let guard := BinaryQuadraticExpressionLifetime.compareWithTrace (parameters.read 2) BinaryRationalOpcode.zero
  if !guard.1 then
    let family := BinaryNestedFamilyLifetime.lotteryWithTrace input (parameters.read 2) K bits
    let assembled := BinaryNestedBinaryAssemblyLifetime.binaryWithTrace (parameters.read 8) family.1 padded.1
    (assembled.1,wrap 40 3 [residual.2,padded.2,guard.2,family.2,assembled.2])
  else
    let finished := BinaryNestedBoundaryLifetime.padWithTrace padded.1
    (finished.1,wrap 40 3 [residual.2,padded.2,guard.2,finished.2])

theorem profileWithTrace_erasure (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithTrace input parameters K bits).1 = BinaryNestedProfileCompiler.thirdProfile input K bits := by
  subst parameters
  let p := BinaryNestedProfileCompiler.parameters input
  let residual := BinaryNestedResidualLifetime.residualWithTrace input p
  let padded := BinaryNestedResidualLifetime.padWithTrace residual.1
  let family := BinaryNestedFamilyLifetime.lotteryWithTrace input (p.read 2) K bits
  have hResidual := BinaryNestedResidualLifetime.residualWithTrace_erasure input p hC rfl
  change residual.1 = _ at hResidual
  have hPadded : padded.1 = BinarySegmentAssembly.padRight (BinaryNestedComponents.residualLottery input) 6 0 := by
    rw [BinaryNestedResidualLifetime.padWithTrace_erasure,hResidual]
  have hFamily := BinaryNestedFamilyLifetime.lotteryWithTrace_erasure input (p.read 2)
    hC (BinaryNestedProfileCompiler.parameters_canonical input hC 2) K bits
  change family.1 = _ at hFamily
  have hPaddedC : padded.1.Canonical := by
    rw [hPadded]
    exact BinarySegmentAssembly.padRight_canonical _ 6 0
      (BinaryNestedComponents.residualLottery_canonical input hC)
  have hFamilyC : family.1.Canonical := by
    rw [hFamily]
    exact BinaryNestedComponents.familyLottery_canonical input _ hC
      (BinaryNestedProfileCompiler.parameters_canonical input hC 2) K bits
  have hAssembly := BinaryNestedBinaryAssemblyLifetime.binaryWithTrace_erasure
    (p.read 8) family.1 padded.1 (BinaryNestedProfileCompiler.parameters_canonical input hC 8)
      hFamilyC hPaddedC
  unfold profileWithTrace BinaryNestedProfileCompiler.thirdProfile
  dsimp only
  simp only [BinaryQuadraticExpressionLifetime.compareWithTrace_erases]
  split
  · rw [hAssembly,hFamily,hPadded]
  · rw [BinaryNestedBoundaryLifetime.padWithTrace_erasure,hPadded]

def envelope (s K : ℕ) : ℕ :=
  BinaryNestedResidualLifetime.envelope s + 2048 +
    BinaryThreeGeometryLifetime.comparisonEnvelope (2 * expressionHeightBudget s 16 + 1) +
    BinaryNestedFamilyLifetime.envelope (expressionHeightBudget s 16) K +
    BinaryNestedBinaryAssemblyLifetime.envelope
      (2 * expressionHeightBudget (max s (K + 2)) 81 + 1) + 4096 + 256

theorem profileWithTrace_usage (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    usage (profileWithTrace input parameters K bits).2 ≤ envelope s K := by
  subst parameters
  let p := BinaryNestedProfileCompiler.parameters input
  let residual := BinaryNestedResidualLifetime.residualWithTrace input p
  let padded := BinaryNestedResidualLifetime.padWithTrace residual.1
  let family := BinaryNestedFamilyLifetime.lotteryWithTrace input (p.read 2) K bits
  let guard := BinaryQuadraticExpressionLifetime.compareWithTrace (p.read 2) BinaryRationalOpcode.zero
  let H := expressionHeightBudget (max s (K + 2)) 81
  have hResidual := BinaryNestedResidualLifetime.residualWithTrace_usage input p hC rfl s hs hH
  change usage residual.2 ≤ _ at hResidual
  have hPad := BinaryNestedResidualLifetime.padWithTrace_usage residual.1
  change usage padded.2 ≤ _ at hPad
  have hP2C := BinaryNestedProfileCompiler.parameters_canonical input hC 2
  have hP2H : RationalHeight (value (p.read 2)) (expressionHeightBudget s 16) :=
    BinaryNestedParameterWork.prepare_height input BinaryRationalOpcode.zero hC
      ⟨BinaryRationalOpcode.zero_valid,by decide⟩ s hs hH (BinaryFactoryHeight.zero_height s hs) 2
  have hInput16 : BinaryNestedParameterWork.InputHeight input (expressionHeightBudget s 16) :=
    BinaryFactoryHeight.InputHeight.mono hH (expressionHeightBudget_ge_input s 16)
  have hFamily := BinaryNestedFamilyLifetime.lotteryWithTrace_usage input (p.read 2) hC hP2C
    _ (hs.trans (expressionHeightBudget_ge_input s 16)) hInput16 hP2H K bits
  change usage family.2 ≤ _ at hFamily
  have hP2W : width (p.read 2) ≤ 2 * expressionHeightBudget s 16 + 1 := by
    have h := hP2C.2.trans (rationalWordWidth_of_height hP2H)
    change width (p.read 2) ≤ _ at h
    omega
  have hZero : width BinaryRationalOpcode.zero ≤ 2 * expressionHeightBudget s 16 + 1 := by
    change 1 ≤ _
    omega
  have hGuard := BinaryThreeGeometryLifetime.comparison_usage (p.read 2) BinaryRationalOpcode.zero
    (2 * expressionHeightBudget s 16 + 1) hP2W hZero
  change usage guard.2 ≤ _ at hGuard
  have hResidualState := BinaryNestedResidualLifetime.residualWithTrace_erasure input p hC rfl
  change residual.1 = _ at hResidualState
  have hPaddedState : padded.1 = BinarySegmentAssembly.padRight (BinaryNestedComponents.residualLottery input) 6 0 := by
    rw [BinaryNestedResidualLifetime.padWithTrace_erasure,hResidualState]
  have hFamilyState := BinaryNestedFamilyLifetime.lotteryWithTrace_erasure input (p.read 2) hC hP2C K bits
  change family.1 = _ at hFamilyState
  have hFamilyC : family.1.Canonical := by
    rw [hFamilyState]
    exact BinaryNestedComponents.familyLottery_canonical input _ hC hP2C K bits
  have hPaddedC : padded.1.Canonical := by
    rw [hPaddedState]
    exact BinarySegmentAssembly.padRight_canonical _ 6 0
      (BinaryNestedComponents.residualLottery_canonical input hC)
  have hFamilyH : BinaryFactoryHeight.SegmentHeight family.1 H := by
    rw [hFamilyState]
    exact BinaryNestedOrderedFactoryWork.family_height input hC s hs hH K bits 2
  have hPaddedH : BinaryFactoryHeight.SegmentHeight padded.1 H := by
    rw [hPaddedState]
    have hr := BinaryNestedRemainingFactoryWork.residual_height input hC (max s (K+2))
      (hs.trans (le_max_left _ _)) (BinaryFactoryHeight.InputHeight.mono hH (le_max_left _ _))
    have hrH := hr.mono (expressionHeightBudget_mono _ (by decide : 24 ≤ 81))
    have hsH : 3 ≤ H := (hs.trans (le_max_left _ _)).trans (expressionHeightBudget_ge_input _ 81)
    exact BinaryAssemblyArithmeticWork.pad_height _ 6 0 H hsH hrH
  have hAlphaC := BinaryNestedProfileCompiler.parameters_canonical input hC 8
  have hAlphaH : RationalHeight (value (p.read 8)) H :=
    (BinaryNestedOrderedFactoryWork.parameter_height input hC s hs hH K 8).mono
      (expressionHeightBudget_mono _ (by decide : 16 ≤ 81))
  have hAlpha : width (p.read 8) ≤ 2*H+1 := by
    have h := hAlphaC.2.trans (rationalWordWidth_of_height hAlphaH)
    change width (p.read 8) ≤ _ at h
    omega
  have hFirst : ∀ j,width (family.1.weight.read j) ≤ 2*H+1 := by
    intro j
    have h := (hFamilyC.1 j).2.trans (rationalWordWidth_of_height (hFamilyH.1 j))
    omega
  have hSecond : ∀ j,width (padded.1.weight.read j) ≤ 2*H+1 := by
    intro j
    have h := (hPaddedC.1 j).2.trans (rationalWordWidth_of_height (hPaddedH.1 j))
    omega
  have hAssembly := BinaryNestedBinaryAssemblyLifetime.binaryWithTrace_usage
    (p.read 8) family.1 padded.1 hAlphaC (2*H+1) (by omega) hAlpha hFirst hSecond
  have hFinished := BinaryNestedBoundaryLifetime.padWithTrace_usage padded.1
  unfold profileWithTrace
  dsimp only
  split
  · have hw := wrap_usage 40 3 [residual.2,padded.2,guard.2,family.2,
      (BinaryNestedBinaryAssemblyLifetime.binaryWithTrace (p.read 8) family.1 padded.1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 40 3 [residual.2,padded.2,guard.2,family.2,
      (BinaryNestedBinaryAssemblyLifetime.binaryWithTrace (p.read 8) family.1 padded.1).2]) ≤ _
    unfold envelope
    dsimp only [H] at hAssembly ⊢
    omega
  · have hw := wrap_usage 40 3 [residual.2,padded.2,guard.2,
      (BinaryNestedBoundaryLifetime.padWithTrace padded.1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 40 3 [residual.2,padded.2,guard.2,
      (BinaryNestedBoundaryLifetime.padWithTrace padded.1).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (profileWithTrace input parameters K bits).2 steps ≤ borrowed + envelope s K ∧
    framePeak ((profileWithTrace input parameters K bits).2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (profileWithTrace_usage input parameters hC hParameters s hs hH K bits) borrowed steps

end Blotto.BinaryNestedThirdProfileLifetime
