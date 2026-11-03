import Blotto.BinaryScalarTape
import Blotto.BinaryNestedBinaryAssemblyLifetime
import Blotto.BinaryNestedOrderedFactoryWork

/-! Complete second ordered interior profile from one already selected
parameter table: a family component, the actual strict mirror guard, and either
a translated-uniform binary mixture or retained eighteen-slot family padding. -/
namespace Blotto.BinaryNestedSecondProfileLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def profileWithTrace (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (K : ℕ) (bits : BinaryScalarTape K) : Segment × Trace :=
  let family := BinaryNestedFamilyLifetime.selectedWithTrace input parameters K bits
  let guard := BinaryQuadraticExpressionLifetime.compareWithTrace input.t (parameters.read 6)
  if !guard.1 then
    let uniform := BinaryNestedSecondUniformLifetime.selectedWithTrace input parameters
    let assembled := BinaryNestedBinaryAssemblyLifetime.binaryWithTrace
      (parameters.read 7) family.1 uniform.1
    (assembled.1,wrap 40 3 [family.2,guard.2,uniform.2,assembled.2])
  else
    let padded := BinaryNestedBoundaryLifetime.padWithTrace family.1
    (padded.1,wrap 40 3 [family.2,guard.2,padded.2])

theorem profileWithTrace_erasure (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithTrace input parameters K bits).1 =
      BinaryNestedProfileCompiler.secondProfile input K bits := by
  subst parameters
  let p := BinaryNestedProfileCompiler.parameters input
  let family := BinaryNestedFamilyLifetime.selectedWithTrace input p K bits
  let uniform := BinaryNestedSecondUniformLifetime.selectedWithTrace input p
  have hFamily := BinaryNestedFamilyLifetime.selectedWithTrace_erasure input p hC rfl K bits
  change family.1 = _ at hFamily
  have hUniform := BinaryNestedSecondUniformLifetime.selectedWithTrace_erasure input p hC rfl
  change uniform.1 = _ at hUniform
  have hFamilyC : family.1.Canonical := by
    rw [hFamily]
    exact BinaryNestedComponents.familyLottery_canonical input _ hC
      (BinaryNestedComponents.mirror_canonical input hC) K bits
  have hUniformC : uniform.1.Canonical := by
    rw [hUniform]
    exact BinaryNestedComponents.secondUniformLottery_canonical input hC
  have hAssembly := BinaryNestedBinaryAssemblyLifetime.binaryWithTrace_erasure
    (p.read 7) family.1 uniform.1
    (BinaryNestedProfileCompiler.parameters_canonical input hC 7) hFamilyC hUniformC
  unfold profileWithTrace BinaryNestedProfileCompiler.secondProfile
  dsimp only
  simp only [BinaryQuadraticExpressionLifetime.compareWithTrace_erases]
  split
  · rw [hAssembly,hFamily,hUniform]
    rfl
  · rw [BinaryNestedBoundaryLifetime.padWithTrace_erasure,hFamily]
    rfl

def envelope (s K : ℕ) : ℕ :=
  BinaryNestedFamilyLifetime.envelope (expressionHeightBudget s 16) K +
    BinaryThreeGeometryLifetime.comparisonEnvelope (2 * expressionHeightBudget s 16 + 1) +
    BinaryNestedSecondUniformLifetime.envelope (expressionHeightBudget s 16) +
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
  let family := BinaryNestedFamilyLifetime.selectedWithTrace input p K bits
  let uniform := BinaryNestedSecondUniformLifetime.selectedWithTrace input p
  let guard := BinaryQuadraticExpressionLifetime.compareWithTrace input.t (p.read 6)
  let H := expressionHeightBudget (max s (K + 2)) 81
  have hFamily := BinaryNestedFamilyLifetime.selectedWithTrace_usage input p hC rfl s hs hH K bits
  change usage family.2 ≤ _ at hFamily
  have hUniform := BinaryNestedSecondUniformLifetime.selectedWithTrace_usage input p hC rfl s hs hH
  change usage uniform.2 ≤ _ at hUniform
  have hMirrorC := BinaryNestedComponents.mirror_canonical input hC
  have hMirrorH := BinaryNestedRemainingFactoryWork.mirror_height input hC s hs hH
  have hT : width input.t ≤ 2 * expressionHeightBudget s 16 + 1 := by
    have h := hC.2.2.2.2.1.2.trans (rationalWordWidth_of_height hH.2.2.2.2.1)
    have hm := expressionHeightBudget_ge_input s 16
    omega
  have hMirror : width (p.read 6) ≤ 2 * expressionHeightBudget s 16 + 1 := by
    have h := hMirrorC.2.trans (rationalWordWidth_of_height hMirrorH)
    change width (BinaryNestedComponents.mirror input) ≤ _
    omega
  have hGuard := BinaryThreeGeometryLifetime.comparison_usage input.t (p.read 6)
    (2 * expressionHeightBudget s 16 + 1) hT hMirror
  change usage guard.2 ≤ _ at hGuard
  have hFamilyState := BinaryNestedFamilyLifetime.selectedWithTrace_erasure input p hC rfl K bits
  change family.1 = _ at hFamilyState
  have hUniformState := BinaryNestedSecondUniformLifetime.selectedWithTrace_erasure input p hC rfl
  change uniform.1 = _ at hUniformState
  have hFamilyC : family.1.Canonical := by
    rw [hFamilyState]
    exact BinaryNestedComponents.familyLottery_canonical input _ hC hMirrorC K bits
  have hUniformC : uniform.1.Canonical := by
    rw [hUniformState]
    exact BinaryNestedComponents.secondUniformLottery_canonical input hC
  have hFamilyH : BinaryFactoryHeight.SegmentHeight family.1 H := by
    rw [hFamilyState]
    exact BinaryNestedOrderedFactoryWork.family_height input hC s hs hH K bits 6
  have hUniformH : BinaryFactoryHeight.SegmentHeight uniform.1 H := by
    rw [hUniformState]
    have hu := BinaryNestedRemainingFactoryWork.second_height input hC (max s (K + 2))
      (hs.trans (le_max_left _ _))
      (BinaryFactoryHeight.InputHeight.mono hH (le_max_left _ _))
    exact hu.mono (expressionHeightBudget_mono _ (by decide : 36 ≤ 81))
  have hAlphaC := BinaryNestedProfileCompiler.parameters_canonical input hC 7
  have hAlphaH : RationalHeight (value (p.read 7)) H :=
    (BinaryNestedOrderedFactoryWork.parameter_height input hC s hs hH K 7).mono
      (expressionHeightBudget_mono _ (by decide : 16 ≤ 81))
  have hAlpha : width (p.read 7) ≤ 2*H+1 := by
    have h := hAlphaC.2.trans (rationalWordWidth_of_height hAlphaH)
    change width (p.read 7) ≤ _ at h
    omega
  have hFirst : ∀ j,width (family.1.weight.read j) ≤ 2*H+1 := by
    intro j
    have h := (hFamilyC.1 j).2.trans (rationalWordWidth_of_height (hFamilyH.1 j))
    omega
  have hSecond : ∀ j,width (uniform.1.weight.read j) ≤ 2*H+1 := by
    intro j
    have h := (hUniformC.1 j).2.trans (rationalWordWidth_of_height (hUniformH.1 j))
    omega
  have hAssembly := BinaryNestedBinaryAssemblyLifetime.binaryWithTrace_usage
    (p.read 7) family.1 uniform.1 hAlphaC (2*H+1) (by omega) hAlpha hFirst hSecond
  have hPad := BinaryNestedBoundaryLifetime.padWithTrace_usage family.1
  unfold profileWithTrace
  dsimp only
  split
  · have hw := wrap_usage 40 3 [family.2,guard.2,uniform.2,
      (BinaryNestedBinaryAssemblyLifetime.binaryWithTrace (p.read 7) family.1 uniform.1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 40 3 [family.2,guard.2,uniform.2,
      (BinaryNestedBinaryAssemblyLifetime.binaryWithTrace (p.read 7) family.1 uniform.1).2]) ≤ _
    unfold envelope
    dsimp only [H] at hAssembly ⊢
    omega
  · have hw := wrap_usage 40 3 [family.2,guard.2,
      (BinaryNestedBoundaryLifetime.padWithTrace family.1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 40 3 [family.2,guard.2,
      (BinaryNestedBoundaryLifetime.padWithTrace family.1).2]) ≤ _
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

end Blotto.BinaryNestedSecondProfileLifetime
