import Blotto.BinaryNestedFirstLocationMeasured
import Blotto.BinaryNestedFirstDescriptorMeasured
import Blotto.BinaryNestedFirstProfileLifetime

/-! The first interior profile consumes one actual measured midpoint/location,
conditional descriptor and eighteen-slot padding. Original canonical fields and
scalar width derive its source work and every-prefix retained bounds. -/
namespace Blotto.BinaryNestedFirstProfileMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def collect (location : (SignedWord × Trace) × ℕ)
    (descriptor : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ)
    (padded : (Segment × Trace) × ℕ) : (Segment × Trace) × ℕ :=
  ((padded.1.1,wrap 40 3 [location.1.2,descriptor.1.2,padded.1.2]),location.2+descriptor.2+padded.2+16)

set_option cleanup.letToHave false in
def profileWithExtras (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : ((Segment × Trace) × ℕ) × ℕ :=
  let location := BinaryNestedFirstLocationMeasured.locationWithExtras input K bits
  let descriptor := BinaryNestedFirstDescriptorMeasured.descriptorWithExtras input location.1.1.1
  let padded := BinaryNestedReferenceMeasured.pad descriptor.1.1.1
  (collect location.1 descriptor.1 padded,location.2+descriptor.2)

def profile (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : (Segment × Trace) × ℕ :=
  (profileWithExtras input K bits).1

theorem profileWithExtras_compat (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input K bits).1 = profile input K bits := rfl

theorem profile_record (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    profile input K bits =
  let location := BinaryNestedFirstLocationMeasured.location input K bits
  let descriptor := BinaryNestedFirstDescriptorMeasured.descriptor input location.1.1
  let padded := BinaryNestedReferenceMeasured.pad descriptor.1.1
  collect location descriptor padded := by
  simp only [profile,profileWithExtras,BinaryNestedFirstLocationMeasured.locationWithExtras_compat,BinaryNestedFirstDescriptorMeasured.positiveFromWithExtras_compat,BinaryNestedFirstDescriptorMeasured.positiveWithExtras_compat,BinaryNestedFirstDescriptorMeasured.fromParametersWithExtras_compat,BinaryNestedFirstDescriptorMeasured.descriptorWithExtras_compat]
  try { split_ifs <;> rfl }

theorem profile_data (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    (profile input K bits).1.1 = (BinaryNestedFirstProfileLifetime.profileWithTrace input K bits).1 := by
  simp only [profile_record,collect,BinaryNestedFirstProfileLifetime.profileWithTrace,
    BinaryNestedFirstLocationMeasured.location_data,BinaryNestedFirstDescriptorMeasured.descriptor_data,
    BinaryNestedReferenceMeasured.pad_data]

def workEnvelope (s K : ℕ) : ℕ := BinaryNestedFirstLocationMeasured.workEnvelope s K+
  BinaryNestedFirstDescriptorMeasured.workEnvelope (expressionHeightBudget (max s (K+2)) 16)+70000+16

def envelope (s K : ℕ) : ℕ := BinaryNestedFirstLocationMeasured.envelope s K+
  BinaryNestedFirstDescriptorMeasured.envelope (expressionHeightBudget (max s (K+2)) 16)+36000+128

theorem collect_bounds (location : (SignedWord × Trace) × ℕ)
    (descriptor : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ)
    (padded : (Segment × Trace) × ℕ) (L D P B U F : ℕ)
    (hl : location.2 ≤ L ∧ usage location.1.2 ≤ B)
    (hd : descriptor.2 ≤ D ∧ usage descriptor.1.2 ≤ U)
    (hp : padded.2 ≤ P ∧ usage padded.1.2 ≤ F) :
    (collect location descriptor padded).2 ≤ L+D+P+16 ∧
      usage (collect location descriptor padded).1.2 ≤ B+U+F+128 := by
  have hw := wrap_usage 40 3 [location.1.2,descriptor.1.2,padded.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change location.2+descriptor.2+padded.2+16 ≤ _ ∧ usage (wrap 40 3 [location.1.2,descriptor.1.2,padded.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem profile_bounds (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (profile input K bits).2 ≤ workEnvelope s K ∧ usage (profile input K bits).1.2 ≤ envelope s K := by
  let W := max s (K+2)
  let H := expressionHeightBudget W 16
  let location := BinaryNestedFirstLocationMeasured.location input K bits
  let descriptor := BinaryNestedFirstDescriptorMeasured.descriptor input location.1.1
  let padded := BinaryNestedReferenceMeasured.pad descriptor.1.1
  have hL := BinaryNestedFirstLocationMeasured.location_bounds input hC s hs hH K bits
  have hState := (BinaryNestedFirstLocationMeasured.location_data input K bits).trans
    (BinaryNestedFirstLocationLifetime.locationWithTrace_erasure input hC K bits)
  have hLC : CanonicalWord location.1.1 := by
    rw [hState]
    exact BinaryNestedFirstConditional.midpointLocation_canonical input hC K bits
  have hLH := BinaryNestedFirstLocationMeasured.location_height input hC s hs hH K bits
  have hIH : BinaryNestedParameterWork.InputHeight input H :=
    BinaryFactoryHeight.InputHeight.mono hH ((le_max_left s (K+2)).trans (expressionHeightBudget_ge_input W 16))
  have hH3 : 3 ≤ H := hs.trans ((le_max_left s (K+2)).trans (expressionHeightBudget_ge_input W 16))
  have hD := BinaryNestedFirstDescriptorMeasured.descriptor_bounds input location.1.1 hC hLC H hH3 hIH hLH
  have hP := BinaryNestedReferenceMeasured.pad_bounds descriptor.1.1
  have hResult := collect_bounds location descriptor padded _ _ _ _ _ _ hL hD hP
  simp only [profile_record]
  simpa only [location,descriptor,padded,H,W,workEnvelope,envelope] using hResult

theorem all_prefix (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (profile input K bits).1.2 steps ≤ borrowed+envelope s K ∧
      framePeak ((profile input K bits).1.2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (profile_bounds input hC s hs hH K bits).2 borrowed steps

end Blotto.BinaryNestedFirstProfileMeasured
