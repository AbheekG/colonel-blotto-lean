import Blotto.BinaryNestedParameterMeasured
import Blotto.BinaryMidpointTapeMeasured
import Blotto.BinaryNestedFirstLocationLifetime

/-! The actual measured Boolean midpoint feeds one measured parameter table;
its returned location word drives the later conditional factory. Original fields
and scalar width bound work and enlarged traces. Native model costs remain. -/
namespace Blotto.BinaryNestedFirstLocationMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 700000

abbrev Input := BinaryNestedParameters.Input

def midpoint (K : ℕ) (bits : BinaryScalarTape K) : (SignedWord × Trace) × ℕ := BinaryMidpointTapeMeasured.sample bits.bits

theorem midpoint_erases (K : ℕ) (bits : BinaryScalarTape K) :
    (midpoint K bits).1 = BinaryNestedFirstLocationLifetime.midpointWithTrace K bits := by
  simp only [midpoint,BinaryMidpointTapeMeasured.sample_erases,BinaryNestedFirstLocationLifetime.midpointWithTrace,
    BinarySegmentPointLifetime.midpointWithTrace]

def collect (K : ℕ) (mid : (SignedWord × Trace) × ℕ) (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ) :
    (SignedWord × Trace) × ℕ :=
  ((parameters.1.1.read 3,wrapList K 32 2 [mid.1.2,parameters.1.2]),mid.2+parameters.2+K+8)

set_option cleanup.letToHave false in
def locationWithExtras (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : ((SignedWord × Trace) × ℕ) × ℕ :=
  let mid := midpoint K bits
  let parameters := BinaryNestedParameterMeasured.prepareAtWithExtras input mid.1.1
  (collect K mid parameters.1,parameters.2)

def location (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : (SignedWord × Trace) × ℕ :=
  (locationWithExtras input K bits).1

theorem locationWithExtras_compat (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    (locationWithExtras input K bits).1 = location input K bits := rfl

theorem location_record (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    location input K bits =
  let mid := midpoint K bits
  let parameters := BinaryNestedParameterMeasured.prepareAt input mid.1.1
  collect K mid parameters := by
  simp only [location,locationWithExtras,BinaryNestedParameterMeasured.runProgramsWithExtras_compat,BinaryNestedParameterMeasured.prepareAtWithExtras_compat,BinaryNestedParameterMeasured.prepareWithExtras_compat,BinaryNestedParameterMeasured.geometryWithExtras_compat]
  try { split_ifs <;> rfl }

theorem location_eq (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : location input K bits =
    let mid := midpoint K bits
    collect K mid (BinaryNestedParameterMeasured.prepareAt input mid.1.1) := by
  simp only [location_record]

theorem location_data (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    (location input K bits).1.1 = (BinaryNestedFirstLocationLifetime.locationWithTrace input K bits).1 := by
  simp only [location_record,collect,BinaryNestedFirstLocationLifetime.locationWithTrace,
    BinaryNestedParameterMeasured.prepareAt_data,midpoint_erases]

def workEnvelope (s K : ℕ) : ℕ := 20*(K+2)+BinaryNestedParameterMeasured.workEnvelope 9 (max s (K+2))+K+8

def envelope (s K : ℕ) : ℕ := 22*K+BinaryNestedParameterMeasured.envelope 9 (max s (K+2)) 128 10+128

theorem collect_bounds (K : ℕ) (mid : (SignedWord × Trace) × ℕ) (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ)
    (P U : ℕ) (hm : mid.2 ≤ 20*(K+2) ∧ usage mid.1.2 ≤ 21*K+58)
    (hp : parameters.2 ≤ P ∧ usage parameters.1.2 ≤ U) :
    (collect K mid parameters).2 ≤ 20*(K+2)+P+K+8 ∧ usage (collect K mid parameters).1.2 ≤ 22*K+U+128 := by
  have hw := wrapList_usage K 32 2 [mid.1.2,parameters.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change mid.2+parameters.2+K+8 ≤ _ ∧ usage (wrapList K 32 2 [mid.1.2,parameters.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem location_bounds (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (location input K bits).2 ≤ workEnvelope s K ∧ usage (location input K bits).1.2 ≤ envelope s K := by
  let W := max s (K+2)
  let mid := midpoint K bits
  let parameters := BinaryNestedParameterMeasured.prepareAt input mid.1.1
  have hMidW : mid.2 ≤ 20*(K+2) := by simpa only [mid,midpoint,BinaryScalarTape.length] using BinaryMidpointTapeMeasured.sample_bound bits.bits
  have hMidU : usage mid.1.2 ≤ 21*K+58 := by
    rw [midpoint_erases]
    exact BinaryNestedFirstLocationLifetime.midpointWithTrace_usage K bits
  have hMidState := (midpoint_erases K bits).trans rfl
  have hMidC : CanonicalWord mid.1.1 := by
    rw [midpoint_erases,BinaryNestedFirstLocationLifetime.midpointWithTrace_erasure]
    exact BinaryDyadicMidpoint.sample_canonical K bits
  have hMidH : RationalHeight (value mid.1.1) W := by
    rw [midpoint_erases,BinaryNestedFirstLocationLifetime.midpointWithTrace_erasure,BinaryDyadicMidpoint.sample_value]
    exact (dyadicMidpointSample_height K bits).mono (le_max_right s (K+2))
  have hInput : BinaryNestedParameterWork.InputHeight input W := BinaryFactoryHeight.InputHeight.mono hH (le_max_left s (K+2))
  have hParams := BinaryNestedParameterMeasured.prepareAt_bounds input mid.1.1 hC hMidC W (hs.trans (le_max_left _ _)) hInput hMidH
  have hResult := collect_bounds K mid parameters _ _ ⟨hMidW,hMidU⟩ hParams
  rw [location_eq]
  simpa only [mid,parameters,W,workEnvelope,envelope] using hResult

theorem location_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    RationalHeight (value (location input K bits).1.1) (expressionHeightBudget (max s (K+2)) 16) := by
  rw [location_data]
  exact BinaryNestedFirstLocationLifetime.locationWithTrace_height input hC s hs hH K bits

theorem all_prefix (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (location input K bits).1.2 steps ≤ borrowed+envelope s K ∧
      framePeak ((location input K bits).1.2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (location_bounds input hC s hs hH K bits).2 borrowed steps

end Blotto.BinaryNestedFirstLocationMeasured
