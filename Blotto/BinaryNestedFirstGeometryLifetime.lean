import Blotto.BinaryScalarTape
import Blotto.BinaryNestedFirstLocationLifetime

/-! The first ordered regime feeds its actually sampled location word into
the four-word regular-three geometry syntax table. -/
namespace Blotto.BinaryNestedFirstGeometryLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input

def geometryWithTrace (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    FixedArrayTable 4 SignedWord × Trace :=
  let location := BinaryNestedFirstLocationLifetime.locationWithTrace input K bits
  let geometry := BinaryNestedParameterAtLifetime.geometryWithTrace input location.1
  (geometry.1,wrap 32 2 [location.2,geometry.2])

theorem geometryWithTrace_erasure (input : Input) (hC : input.Canonical)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (geometryWithTrace input K bits).1 =
      BinaryNestedParameters.geometry input (BinaryNestedFirstConditional.midpointLocation input K bits) := by
  have hLocation := BinaryNestedFirstLocationLifetime.locationWithTrace_erasure input hC K bits
  have hLocationC : CanonicalWord (BinaryNestedFirstLocationLifetime.locationWithTrace input K bits).1 := by
    rw [hLocation]
    exact BinaryNestedFirstConditional.midpointLocation_canonical input hC K bits
  have hGeometry := BinaryNestedParameterAtLifetime.geometryWithTrace_erasure input
    (BinaryNestedFirstLocationLifetime.locationWithTrace input K bits).1 hC hLocationC
  unfold geometryWithTrace
  dsimp only
  rw [hGeometry,hLocation]

def envelope (s K : ℕ) : ℕ :=
  BinaryNestedFirstLocationLifetime.envelope s K +
    BinaryNestedParameterAtLifetime.geometryEnvelope
      (expressionHeightBudget (max s (K + 2)) 16) + 64

theorem geometryWithTrace_usage (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    usage (geometryWithTrace input K bits).2 ≤ envelope s K := by
  let W := max s (K + 2)
  let H := expressionHeightBudget W 16
  let location := BinaryNestedFirstLocationLifetime.locationWithTrace input K bits
  have hLocation := BinaryNestedFirstLocationLifetime.locationWithTrace_usage input hC s hs hH K bits
  change usage location.2 ≤ _ at hLocation
  have hLocationState := BinaryNestedFirstLocationLifetime.locationWithTrace_erasure input hC K bits
  have hLocationC : CanonicalWord location.1 := by
    rw [hLocationState]
    exact BinaryNestedFirstConditional.midpointLocation_canonical input hC K bits
  have hLocationH : RationalHeight (value location.1) H := by
    exact BinaryNestedFirstLocationLifetime.locationWithTrace_height input hC s hs hH K bits
  have hInputW : BinaryNestedParameterWork.InputHeight input W :=
    BinaryFactoryHeight.InputHeight.mono hH (le_max_left s (K + 2))
  have hInputH : BinaryNestedParameterWork.InputHeight input H :=
    BinaryFactoryHeight.InputHeight.mono hInputW (expressionHeightBudget_ge_input W 16)
  have hGeometry := BinaryNestedParameterAtLifetime.geometryWithTrace_usage input location.1
    hC hLocationC H
    ((hs.trans (le_max_left s (K + 2))).trans (expressionHeightBudget_ge_input W 16))
    hInputH hLocationH
  have hw := wrap_usage 32 2
    [location.2,(BinaryNestedParameterAtLifetime.geometryWithTrace input location.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2
    [location.2,(BinaryNestedParameterAtLifetime.geometryWithTrace input location.1).2]) ≤ _
  unfold envelope
  dsimp only [W,H] at hGeometry ⊢
  omega

theorem all_prefix (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (geometryWithTrace input K bits).2 steps ≤ borrowed + envelope s K ∧
    framePeak ((geometryWithTrace input K bits).2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (geometryWithTrace_usage input hC s hs hH K bits) borrowed steps

end Blotto.BinaryNestedFirstGeometryLifetime
