import Blotto.BinaryScalarTape
import Blotto.BinaryNestedParameterAtLifetime
import Blotto.BinarySegmentPointLifetime

/-! The first ordered nested regime constructs its midpoint from Boolean bits
and evaluates the actual location parameter on that returned word. -/
namespace Blotto.BinaryNestedFirstLocationLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input

def midpointWithTrace (K : ℕ) (bits : BinaryScalarTape K) : SignedWord × Trace :=
  BinarySegmentPointLifetime.midpointWithTrace bits.bits

theorem midpointWithTrace_erasure (K : ℕ) (bits : BinaryScalarTape K) :
    (midpointWithTrace K bits).1 = BinaryDyadicMidpoint.sample K bits := by
  rw [midpointWithTrace,BinarySegmentPointLifetime.midpointWithTrace_erases,
    ← bits.listOfFn_read,BinaryDirectDyadicMidpoint.sample_ofFn]

theorem midpointWithTrace_usage (K : ℕ) (bits : BinaryScalarTape K) :
    usage (midpointWithTrace K bits).2 ≤ 21 * K + 58 := by
  have h := BinarySegmentPointLifetime.midpointWithTrace_bounds bits.bits
  simp only [BinaryScalarTape.length] at h
  unfold midpointWithTrace usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

def locationWithTrace (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : SignedWord × Trace :=
  let midpoint := midpointWithTrace K bits
  let parameters := BinaryNestedParameterAtLifetime.prepareWithTrace input midpoint.1
  (parameters.1.read 3,wrapList K 32 2 [midpoint.2,parameters.2])

theorem locationWithTrace_erasure (input : Input) (hC : input.Canonical)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (locationWithTrace input K bits).1 = BinaryNestedFirstConditional.midpointLocation input K bits := by
  have hMidpoint := midpointWithTrace_erasure K bits
  have hCanonical : CanonicalWord (midpointWithTrace K bits).1 := by
    rw [hMidpoint]
    exact BinaryDyadicMidpoint.sample_canonical K bits
  have hParameters := BinaryNestedParameterAtLifetime.prepareWithTrace_erasure input
    (midpointWithTrace K bits).1 hC hCanonical
  unfold locationWithTrace BinaryNestedFirstConditional.midpointLocation
  dsimp only
  rw [hParameters,hMidpoint]

def envelope (s K : ℕ) : ℕ :=
  22 * K + BinaryNestedParameterLifetime.envelope (max s (K + 2)) + 128

theorem locationWithTrace_usage (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    usage (locationWithTrace input K bits).2 ≤ envelope s K := by
  let W := max s (K + 2)
  let midpoint := midpointWithTrace K bits
  have hMidpoint := midpointWithTrace_usage K bits
  change usage midpoint.2 ≤ _ at hMidpoint
  have hMidpointState := midpointWithTrace_erasure K bits
  have hMidpointC : CanonicalWord midpoint.1 := by
    rw [hMidpointState]
    exact BinaryDyadicMidpoint.sample_canonical K bits
  have hMidpointH : RationalHeight (value midpoint.1) W := by
    rw [hMidpointState,BinaryDyadicMidpoint.sample_value]
    exact (dyadicMidpointSample_height K bits).mono (le_max_right s (K + 2))
  have hInput : BinaryNestedParameterWork.InputHeight input W :=
    BinaryFactoryHeight.InputHeight.mono hH (le_max_left s (K + 2))
  have hParameters := BinaryNestedParameterAtLifetime.prepareWithTrace_usage input midpoint.1
    hC hMidpointC W (hs.trans (le_max_left _ _)) hInput hMidpointH
  have hw := wrapList_usage K 32 2
    [midpoint.2,(BinaryNestedParameterAtLifetime.prepareWithTrace input midpoint.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrapList K 32 2
    [midpoint.2,(BinaryNestedParameterAtLifetime.prepareWithTrace input midpoint.1).2]) ≤ _
  unfold envelope
  dsimp only [W] at hParameters ⊢
  omega

theorem locationWithTrace_height (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    RationalHeight (value (locationWithTrace input K bits).1)
      (expressionHeightBudget (max s (K + 2)) 16) := by
  rw [locationWithTrace_erasure input hC K bits]
  let W := max s (K + 2)
  have hInput : BinaryNestedParameterWork.InputHeight input W :=
    BinaryFactoryHeight.InputHeight.mono hH (le_max_left s (K + 2))
  have hScalar : RationalHeight (value (BinaryDyadicMidpoint.sample K bits)) W := by
    rw [BinaryDyadicMidpoint.sample_value]
    exact (dyadicMidpointSample_height K bits).mono (le_max_right s (K + 2))
  exact BinaryNestedParameterWork.prepare_height input _ hC
    (BinaryDyadicMidpoint.sample_canonical K bits) W
    (hs.trans (le_max_left _ _)) hInput hScalar 3

theorem all_prefix (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (locationWithTrace input K bits).2 steps ≤ borrowed + envelope s K ∧
    framePeak ((locationWithTrace input K bits).2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (locationWithTrace_usage input hC s hs hH K bits) borrowed steps

end Blotto.BinaryNestedFirstLocationLifetime
