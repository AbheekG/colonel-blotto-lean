import Blotto.BinaryScalarTape
import Blotto.BinaryNestedFirstDescriptorLifetime

/-! The selected first ordered interior regime: one actual Boolean midpoint,
location, conditional descriptor and retained eighteen-slot padding. -/
namespace Blotto.BinaryNestedFirstProfileLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def profileWithTrace (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : Segment × Trace :=
  let location := BinaryNestedFirstLocationLifetime.locationWithTrace input K bits
  let descriptor := BinaryNestedFirstDescriptorLifetime.descriptorWithTrace input location.1
  let padded := BinaryNestedBoundaryLifetime.padWithTrace descriptor.1
  (padded.1,wrap 40 3 [location.2,descriptor.2,padded.2])

theorem profileWithTrace_erasure (input : Input) (hC : input.Canonical)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithTrace input K bits).1 =
      BinarySegmentAssembly.padRight (BinaryNestedFirstConditional.firstProfile input K bits) 9 0 := by
  have hLocation := BinaryNestedFirstLocationLifetime.locationWithTrace_erasure input hC K bits
  have hLocationC : CanonicalWord (BinaryNestedFirstLocationLifetime.locationWithTrace input K bits).1 := by
    rw [hLocation]
    exact BinaryNestedFirstConditional.midpointLocation_canonical input hC K bits
  have hDescriptor := BinaryNestedFirstDescriptorLifetime.descriptorWithTrace_erasure input
    (BinaryNestedFirstLocationLifetime.locationWithTrace input K bits).1 hC hLocationC
  unfold profileWithTrace BinaryNestedFirstConditional.firstProfile
  dsimp only
  rw [BinaryNestedBoundaryLifetime.padWithTrace_erasure,hDescriptor,hLocation]

def envelope (s K : ℕ) : ℕ :=
  BinaryNestedFirstLocationLifetime.envelope s K +
    BinaryNestedFirstDescriptorLifetime.envelope
      (expressionHeightBudget (max s (K + 2)) 16) + 4096 + 128

theorem profileWithTrace_usage (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    usage (profileWithTrace input K bits).2 ≤ envelope s K := by
  let W := max s (K + 2)
  let H := expressionHeightBudget W 16
  let location := BinaryNestedFirstLocationLifetime.locationWithTrace input K bits
  let descriptor := BinaryNestedFirstDescriptorLifetime.descriptorWithTrace input location.1
  have hLocation := BinaryNestedFirstLocationLifetime.locationWithTrace_usage input hC s hs hH K bits
  change usage location.2 ≤ _ at hLocation
  have hLocationState := BinaryNestedFirstLocationLifetime.locationWithTrace_erasure input hC K bits
  have hLocationC : CanonicalWord location.1 := by
    rw [hLocationState]
    exact BinaryNestedFirstConditional.midpointLocation_canonical input hC K bits
  have hLocationH : RationalHeight (value location.1) H :=
    BinaryNestedFirstLocationLifetime.locationWithTrace_height input hC s hs hH K bits
  have hInputW : BinaryNestedParameterWork.InputHeight input W :=
    BinaryFactoryHeight.InputHeight.mono hH (le_max_left s (K + 2))
  have hInputH : BinaryNestedParameterWork.InputHeight input H :=
    BinaryFactoryHeight.InputHeight.mono hInputW (expressionHeightBudget_ge_input W 16)
  have hDescriptor := BinaryNestedFirstDescriptorLifetime.descriptorWithTrace_usage input location.1
    hC hLocationC H ((hs.trans (le_max_left s (K + 2))).trans
      (expressionHeightBudget_ge_input W 16)) hInputH hLocationH
  change usage descriptor.2 ≤ _ at hDescriptor
  have hPadded := BinaryNestedBoundaryLifetime.padWithTrace_usage descriptor.1
  have hw := wrap_usage 40 3
    [location.2,descriptor.2,(BinaryNestedBoundaryLifetime.padWithTrace descriptor.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 40 3
    [location.2,descriptor.2,(BinaryNestedBoundaryLifetime.padWithTrace descriptor.1).2]) ≤ _
  unfold envelope
  dsimp only [W,H] at hDescriptor ⊢
  omega

theorem all_prefix (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (profileWithTrace input K bits).2 steps ≤ borrowed + envelope s K ∧
    framePeak ((profileWithTrace input K bits).2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (profileWithTrace_usage input hC s hs hH K bits) borrowed steps

end Blotto.BinaryNestedFirstProfileLifetime
