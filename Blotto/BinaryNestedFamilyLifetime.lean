import Blotto.BinaryScalarTape
import Blotto.BinaryNestedFirstProfileLifetime
import Blotto.BinaryNestedFamilyFactoryWork
import Blotto.BinaryNestedRemainingFactoryWork

/-! The selected family component constructs its substituted input, midpoint
location and complete first-conditional nine-slot lottery with actual traces. -/
namespace Blotto.BinaryNestedFamilyLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 9

def inputWithTrace (input : Input) (length : SignedWord) : Input × Trace :=
  let parameters := BinaryNestedParameterAtLifetime.prepareWithTrace input length
  (⟨input.M,input.a,input.d,input.c,length,parameters.1.read 5⟩,
    wrap 32 2 [parameters.2])

theorem inputWithTrace_erasure (input : Input) (length : SignedWord)
    (hC : input.Canonical) (hL : CanonicalWord length) :
    (inputWithTrace input length).1 = BinaryNestedComponents.familyInput input length := by
  simp only [inputWithTrace,BinaryNestedComponents.familyInput,
    BinaryNestedParameterAtLifetime.prepareWithTrace_erasure input length hC hL]

def inputEnvelope (s : ℕ) : ℕ := BinaryNestedParameterLifetime.envelope s + 64

theorem inputWithTrace_usage (input : Input) (length : SignedWord)
    (hC : input.Canonical) (hL : CanonicalWord length)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hLength : RationalHeight (value length) s) :
    usage (inputWithTrace input length).2 ≤ inputEnvelope s := by
  have hp := BinaryNestedParameterAtLifetime.prepareWithTrace_usage input length
    hC hL s hs hH hLength
  have hw := wrap_usage 32 2
    [(BinaryNestedParameterAtLifetime.prepareWithTrace input length).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2
    [(BinaryNestedParameterAtLifetime.prepareWithTrace input length).2]) ≤ _
  unfold inputEnvelope
  omega

def lotteryWithTrace (input : Input) (length : SignedWord)
    (K : ℕ) (bits : BinaryScalarTape K) : Segment × Trace :=
  let family := inputWithTrace input length
  let location := BinaryNestedFirstLocationLifetime.locationWithTrace family.1 K bits
  let descriptor := BinaryNestedFirstDescriptorLifetime.descriptorWithTrace family.1 location.1
  (descriptor.1,wrap 40 3 [family.2,location.2,descriptor.2])

theorem lotteryWithTrace_erasure (input : Input) (length : SignedWord)
    (hC : input.Canonical) (hL : CanonicalWord length)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (lotteryWithTrace input length K bits).1 =
      BinaryNestedComponents.familyLottery input length K bits := by
  let family := inputWithTrace input length
  have hFamily := inputWithTrace_erasure input length hC hL
  change family.1 = _ at hFamily
  have hFamilyC : family.1.Canonical := by
    rw [hFamily]
    exact BinaryNestedComponents.familyInput_canonical input length hC hL
  have hLocation := BinaryNestedFirstLocationLifetime.locationWithTrace_erasure
    family.1 hFamilyC K bits
  have hLocationC : CanonicalWord
      (BinaryNestedFirstLocationLifetime.locationWithTrace family.1 K bits).1 := by
    rw [hLocation]
    exact BinaryNestedFirstConditional.midpointLocation_canonical family.1 hFamilyC K bits
  have hDescriptor := BinaryNestedFirstDescriptorLifetime.descriptorWithTrace_erasure
    family.1 (BinaryNestedFirstLocationLifetime.locationWithTrace family.1 K bits).1
    hFamilyC hLocationC
  unfold lotteryWithTrace BinaryNestedComponents.familyLottery
    BinaryNestedFirstConditional.firstProfile
  dsimp only
  rw [hDescriptor,hLocation,hFamily]

def envelope (s K : ℕ) : ℕ :=
  let H := expressionHeightBudget s 16
  let W := max H (K + 2)
  inputEnvelope s + BinaryNestedFirstLocationLifetime.envelope H K +
    BinaryNestedFirstDescriptorLifetime.envelope (expressionHeightBudget W 16) + 256

theorem lotteryWithTrace_usage (input : Input) (length : SignedWord)
    (hC : input.Canonical) (hL : CanonicalWord length)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hLength : RationalHeight (value length) s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    usage (lotteryWithTrace input length K bits).2 ≤ envelope s K := by
  let H := expressionHeightBudget s 16
  let W := max H (K + 2)
  let T := expressionHeightBudget W 16
  let family := inputWithTrace input length
  let location := BinaryNestedFirstLocationLifetime.locationWithTrace family.1 K bits
  let descriptor := BinaryNestedFirstDescriptorLifetime.descriptorWithTrace family.1 location.1
  have hFamily := inputWithTrace_usage input length hC hL s hs hH hLength
  change usage family.2 ≤ _ at hFamily
  have hFamilyState := inputWithTrace_erasure input length hC hL
  change family.1 = _ at hFamilyState
  have hFamilyC : family.1.Canonical := by
    rw [hFamilyState]
    exact BinaryNestedComponents.familyInput_canonical input length hC hL
  have hFamilyH : BinaryNestedParameterWork.InputHeight family.1 H := by
    rw [hFamilyState]
    exact BinaryNestedFamilyFactoryWork.family_input_height input length
      hC hL s hs hH hLength
  have hsH : 3 ≤ H := hs.trans (expressionHeightBudget_ge_input s 16)
  have hLocation := BinaryNestedFirstLocationLifetime.locationWithTrace_usage
    family.1 hFamilyC H hsH hFamilyH K bits
  change usage location.2 ≤ _ at hLocation
  change usage location.2 ≤
    BinaryNestedFirstLocationLifetime.envelope (expressionHeightBudget s 16) K at hLocation
  have hLocationState := BinaryNestedFirstLocationLifetime.locationWithTrace_erasure
    family.1 hFamilyC K bits
  have hLocationC : CanonicalWord location.1 := by
    rw [hLocationState]
    exact BinaryNestedFirstConditional.midpointLocation_canonical family.1 hFamilyC K bits
  have hLocationH : RationalHeight (value location.1) T :=
    BinaryNestedFirstLocationLifetime.locationWithTrace_height
      family.1 hFamilyC H hsH hFamilyH K bits
  have hFamilyW : BinaryNestedParameterWork.InputHeight family.1 W :=
    BinaryFactoryHeight.InputHeight.mono hFamilyH (le_max_left H (K + 2))
  have hFamilyT : BinaryNestedParameterWork.InputHeight family.1 T :=
    BinaryFactoryHeight.InputHeight.mono hFamilyW (expressionHeightBudget_ge_input W 16)
  have hsT : 3 ≤ T := (hsH.trans (le_max_left H (K + 2))).trans
    (expressionHeightBudget_ge_input W 16)
  have hDescriptor := BinaryNestedFirstDescriptorLifetime.descriptorWithTrace_usage
    family.1 location.1 hFamilyC hLocationC T hsT hFamilyT hLocationH
  change usage descriptor.2 ≤ _ at hDescriptor
  have hw := wrap_usage 40 3 [family.2,location.2,descriptor.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 40 3 [family.2,location.2,descriptor.2]) ≤ _
  unfold envelope
  dsimp only [H,W,T] at hDescriptor ⊢
  omega

theorem all_prefix (input : Input) (length : SignedWord)
    (hC : input.Canonical) (hL : CanonicalWord length)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hLength : RationalHeight (value length) s)
    (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (lotteryWithTrace input length K bits).2 steps ≤
      borrowed + envelope s K ∧
    framePeak ((lotteryWithTrace input length K bits).2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (lotteryWithTrace_usage input length hC hL s hs hH hLength K bits) borrowed steps

def selectedWithTrace (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (K : ℕ) (bits : BinaryScalarTape K) : Segment × Trace :=
  lotteryWithTrace input (parameters.read 6) K bits

theorem selectedWithTrace_erasure (input : Input)
    (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (selectedWithTrace input parameters K bits).1 =
      BinaryNestedComponents.familyLottery input (BinaryNestedComponents.mirror input) K bits := by
  subst parameters
  exact lotteryWithTrace_erasure input (BinaryNestedComponents.mirror input)
    hC (BinaryNestedComponents.mirror_canonical input hC) K bits

theorem selectedWithTrace_usage (input : Input)
    (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    usage (selectedWithTrace input parameters K bits).2 ≤
      envelope (expressionHeightBudget s 16) K := by
  subst parameters
  let H := expressionHeightBudget s 16
  have hMirrorC := BinaryNestedComponents.mirror_canonical input hC
  have hMirrorH := BinaryNestedRemainingFactoryWork.mirror_height input hC s hs hH
  have hInputH : BinaryNestedParameterWork.InputHeight input H :=
    BinaryFactoryHeight.InputHeight.mono hH (expressionHeightBudget_ge_input s 16)
  have hsH : 3 ≤ H := hs.trans (expressionHeightBudget_ge_input s 16)
  change usage (lotteryWithTrace input (BinaryNestedComponents.mirror input) K bits).2 ≤ _
  exact lotteryWithTrace_usage input (BinaryNestedComponents.mirror input)
    hC hMirrorC H hsH hInputH hMirrorH K bits

theorem selected_all_prefix (input : Input)
    (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (selectedWithTrace input parameters K bits).2 steps ≤
      borrowed + envelope (expressionHeightBudget s 16) K ∧
    framePeak ((selectedWithTrace input parameters K bits).2.take steps) ≤
      envelope (expressionHeightBudget s 16) K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (selectedWithTrace_usage input parameters hC hParameters s hs hH K bits) borrowed steps

end Blotto.BinaryNestedFamilyLifetime
