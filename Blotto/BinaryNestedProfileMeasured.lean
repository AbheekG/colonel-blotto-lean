import Blotto.BinaryNestedThirdProfileMeasured
import Blotto.BinaryNestedControlMeasured

/-! Complete measured nested profiles execute one boundary/order/parameter/
regime prefix, only its selected interior producer, and coordinate restoration.
Original canonical nested fields and scalar width derive joined source bounds. -/
namespace Blotto.BinaryNestedProfileMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1500000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def retain (child : (Segment × Trace) × ℕ) : (Segment × Trace) × ℕ :=
  ((child.1.1,wrap 24 2 [child.1.2]),child.2+4)

set_option cleanup.letToHave false in
def orderedWithExtras (input : Input) (parameters : FixedArrayTable 9 SignedWord) (regime : Fin 3) (K : ℕ) (bits : BinaryScalarTape K) : ((Segment × Trace) × ℕ) × ℕ :=
  let chosen := if regime = 0 then BinaryNestedFirstProfileMeasured.profileWithExtras input K bits
    else if regime = 1 then BinaryNestedSecondProfileMeasured.profileWithExtras input parameters K bits
    else BinaryNestedThirdProfileMeasured.profileWithExtras input parameters K bits
  (retain chosen.1,chosen.2)

def ordered (input : Input) (parameters : FixedArrayTable 9 SignedWord) (regime : Fin 3) (K : ℕ) (bits : BinaryScalarTape K) :
    (Segment × Trace) × ℕ :=
  (orderedWithExtras input parameters regime K bits).1

theorem orderedWithExtras_compat (input : Input) (parameters : FixedArrayTable 9 SignedWord) (regime : Fin 3) (K : ℕ) (bits : BinaryScalarTape K) :
    (orderedWithExtras input parameters regime K bits).1 = ordered input parameters regime K bits := rfl

theorem ordered_record (input : Input) (parameters : FixedArrayTable 9 SignedWord) (regime : Fin 3) (K : ℕ) (bits : BinaryScalarTape K) :
    ordered input parameters regime K bits =
  if regime = 0 then retain (BinaryNestedFirstProfileMeasured.profile input K bits)
  else if regime = 1 then retain (BinaryNestedSecondProfileMeasured.profile input parameters K bits)
  else retain (BinaryNestedThirdProfileMeasured.profile input parameters K bits) := by
  simp only [ordered,orderedWithExtras,BinaryNestedControlMeasured.classifyWithExtras_compat,BinaryNestedControlMeasured.interiorWithExtras_compat,BinaryNestedControlMeasured.runWithExtras_compat,BinaryNestedFirstProfileMeasured.profileWithExtras_compat,BinaryNestedSecondProfileMeasured.mixWithExtras_compat,BinaryNestedSecondProfileMeasured.profileWithExtras_compat,BinaryNestedThirdProfileMeasured.mixWithExtras_compat,BinaryNestedThirdProfileMeasured.profileWithExtras_compat]
  try { split_ifs <;> rfl }

theorem ordered_data (input : Input) (parameters : FixedArrayTable 9 SignedWord) (regime : Fin 3) (K : ℕ) (bits : BinaryScalarTape K) :
    (ordered input parameters regime K bits).1.1 = (BinaryNestedProfileLifetime.orderedWithTrace input parameters regime K bits).1 := by
  simp only [ordered_record]
  unfold BinaryNestedProfileLifetime.orderedWithTrace
  split_ifs <;> simp only [retain,BinaryNestedFirstProfileMeasured.profile_data,BinaryNestedSecondProfileMeasured.profile_data,
    BinaryNestedThirdProfileMeasured.profile_data]

def orderedPrice (s K : ℕ) : ℕ := BinaryNestedFirstProfileMeasured.workEnvelope s K+
  BinaryNestedSecondProfileMeasured.workEnvelope s K+BinaryNestedThirdProfileMeasured.workEnvelope s K+4

def orderedEnvelope (s K : ℕ) : ℕ := BinaryNestedFirstProfileMeasured.envelope s K+
  BinaryNestedSecondProfileMeasured.envelope s K+BinaryNestedThirdProfileMeasured.envelope s K+64

theorem retain_bounds (child : (Segment × Trace) × ℕ) (P U : ℕ) (h : child.2 ≤ P ∧ usage child.1.2 ≤ U) :
    (retain child).2 ≤ P+4 ∧ usage (retain child).1.2 ≤ U+64 := by
  have hw := wrap_usage 24 2 [child.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change child.2+4 ≤ _ ∧ usage (wrap 24 2 [child.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem ordered_bounds (input : Input) (parameters : FixedArrayTable 9 SignedWord) (regime : Fin 3) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (ordered input parameters regime K bits).2 ≤ orderedPrice s K ∧ usage (ordered input parameters regime K bits).1.2 ≤ orderedEnvelope s K := by
  have hFirst := retain_bounds (BinaryNestedFirstProfileMeasured.profile input K bits) _ _
    (BinaryNestedFirstProfileMeasured.profile_bounds input hC s hs hH K bits)
  have hSecond := retain_bounds (BinaryNestedSecondProfileMeasured.profile input parameters K bits) _ _
    (BinaryNestedSecondProfileMeasured.profile_bounds input parameters hC hParameters s hs hH K bits)
  have hThird := retain_bounds (BinaryNestedThirdProfileMeasured.profile input parameters K bits) _ _
    (BinaryNestedThirdProfileMeasured.profile_bounds input parameters hC hParameters s hs hH K bits)
  simp only [ordered_record]
  split
  · unfold orderedPrice orderedEnvelope; exact ⟨by omega,by omega⟩
  · split <;> unfold orderedPrice orderedEnvelope <;> exact ⟨by omega,by omega⟩

set_option cleanup.letToHave false in
def profileWithExtras (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : ((Segment × Trace) × ℕ) × ℕ :=
  let prior := BinaryNestedControlMeasured.runWithExtras input
  match prior.1.1.1 with
  | Sum.inl table => (((table,wrap 24 2 [prior.1.1.2]),prior.1.2+4),prior.2)
  | Sum.inr selected =>
      let child := orderedWithExtras selected.1.1.1 selected.1.2 selected.2 K bits
      (BinaryNestedReferenceMeasured.restore selected.1.1.2 prior.1 child.1,prior.2+child.2)

def profile (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : (Segment × Trace) × ℕ :=
  (profileWithExtras input K bits).1

theorem profileWithExtras_compat (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input K bits).1 = profile input K bits := rfl

theorem profile_record (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    profile input K bits =
  let prior := BinaryNestedControlMeasured.run input
  match prior.1.1 with
  | Sum.inl table => ((table,wrap 24 2 [prior.1.2]),prior.2+4)
  | Sum.inr selected =>
      let child := ordered selected.1.1.1 selected.1.2 selected.2 K bits
      BinaryNestedReferenceMeasured.restore selected.1.1.2 prior child := by
  simp only [profile,profileWithExtras,BinaryNestedControlMeasured.classifyWithExtras_compat,BinaryNestedControlMeasured.interiorWithExtras_compat,BinaryNestedControlMeasured.runWithExtras_compat,BinaryNestedFirstProfileMeasured.profileWithExtras_compat,BinaryNestedSecondProfileMeasured.mixWithExtras_compat,BinaryNestedSecondProfileMeasured.profileWithExtras_compat,BinaryNestedThirdProfileMeasured.mixWithExtras_compat,BinaryNestedThirdProfileMeasured.profileWithExtras_compat,orderedWithExtras_compat]
  cases h : (BinaryNestedControlMeasured.run input).1.1 <;> simp only [h]

theorem profile_data (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    (profile input K bits).1.1 = (BinaryNestedProfileLifetime.profileWithTrace input K bits).1 := by
  simp only [profile_record,BinaryNestedProfileLifetime.profileWithTrace,BinaryNestedControlMeasured.run_data]
  cases h : (BinaryNestedSelectedRegimePrefixLifetime.runWithTrace input).1 with
  | inl table => simp only
  | inr selected =>
      simp only [BinaryNestedReferenceMeasured.restore_data,BinaryNestedOrderLifetime.restoreWithTrace_erasure,ordered_data]

theorem profile_erasure (input : Input) (hC : input.Canonical) (K : ℕ) (bits : BinaryScalarTape K) :
    (profile input K bits).1.1 = BinaryNestedSpecProfile.profile input K bits :=
  (profile_data input K bits).trans (BinaryNestedProfileLifetime.profileWithTrace_erasure input hC K bits)

def workEnvelope (s K : ℕ) : ℕ := BinaryNestedControlMeasured.workEnvelope s+orderedPrice s K+85000+16

def envelope (s K : ℕ) : ℕ := BinaryNestedControlMeasured.envelope s+orderedEnvelope s K+50000+96

theorem profile_bounds (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (profile input K bits).2 ≤ workEnvelope s K ∧ usage (profile input K bits).1.2 ≤ envelope s K := by
  let prior := BinaryNestedControlMeasured.run input
  have hPrior := BinaryNestedControlMeasured.run_bounds input hC s hs hH
  change prior.2 ≤ _ ∧ usage prior.1.2 ≤ _ at hPrior
  simp only [profile_record]

  split
  · have hw := wrap_usage 24 2 [prior.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change prior.2+4 ≤ _ ∧ usage (wrap 24 2 [prior.1.2]) ≤ _
    unfold workEnvelope envelope; exact ⟨by omega,by omega⟩
  · rename_i selected hSelected
    have hContract := BinaryNestedControlMeasured.selected_contract input hC selected hSelected
    have hSortedC : selected.1.1.1.Canonical := by rw [hContract.1]; exact BinaryNestedTerminalInput.sortedInput_canonical input hC
    have hSortedH : BinaryNestedParameterWork.InputHeight selected.1.1.1 s := by
      rw [hContract.1]; exact BinaryNestedSpecFactoryWork.sortedInput_height input hC s hH
    have hChild := ordered_bounds selected.1.1.1 selected.1.2 selected.2 hSortedC hContract.2.2.1 s hs hSortedH K bits
    exact BinaryNestedReferenceMeasured.restore_bounds selected.1.1.2 prior _ _ _ _ _ hPrior hChild

theorem profile_canonical (input : Input) (hC : input.Canonical) (K : ℕ) (bits : BinaryScalarTape K) :
    (profile input K bits).1.1.Canonical := by
  rw [profile_data]; exact BinaryNestedProfileLifetime.profileWithTrace_canonical input hC K bits

theorem profile_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    BinaryFactoryHeight.SegmentHeight (profile input K bits).1.1 (BinaryNestedOrderedFactoryWork.height s K 83) := by
  rw [profile_data]; exact BinaryNestedProfileLifetime.profileWithTrace_height input hC s hs hH K bits

theorem all_prefix (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (profile input K bits).1.2 steps ≤ borrowed+envelope s K ∧ framePeak ((profile input K bits).1.2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (profile_bounds input hC s hs hH K bits).2 borrowed steps

end Blotto.BinaryNestedProfileMeasured
