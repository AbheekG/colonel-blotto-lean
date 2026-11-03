import Blotto.BinaryNestedFirstProfileMeasured
import Blotto.BinaryNestedFamilyLifetime

/-! A measured substituted input feeds one actual measured location and
conditional nine-slot descriptor. Original input/length heights derive the
complete family component's source-work and retained-prefix bounds. -/
namespace Blotto.BinaryNestedFamilyMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 9

def inputFrom (input : Input) (length : SignedWord) (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ) :
    (Input × Trace) × ℕ :=
  ((⟨input.M,input.a,input.d,input.c,length,parameters.1.1.read 5⟩,wrap 32 2 [parameters.1.2]),parameters.2+8)

set_option cleanup.letToHave false in
def prepareWithExtras (input : Input) (length : SignedWord) : ((Input × Trace) × ℕ) × ℕ :=
  let parameters := BinaryNestedParameterMeasured.prepareAtWithExtras input length
  (inputFrom input length parameters.1,parameters.2)

def prepare (input : Input) (length : SignedWord) : (Input × Trace) × ℕ :=
  (prepareWithExtras input length).1

theorem prepareWithExtras_compat (input : Input) (length : SignedWord) :
    (prepareWithExtras input length).1 = prepare input length := rfl

theorem prepare_record (input : Input) (length : SignedWord) :
    prepare input length =
  inputFrom input length (BinaryNestedParameterMeasured.prepareAt input length) := by
  simp only [prepare,prepareWithExtras,BinaryNestedParameterMeasured.runProgramsWithExtras_compat,BinaryNestedParameterMeasured.prepareAtWithExtras_compat,BinaryNestedParameterMeasured.prepareWithExtras_compat,BinaryNestedParameterMeasured.geometryWithExtras_compat,BinaryNestedFirstLocationMeasured.locationWithExtras_compat,BinaryNestedFirstDescriptorMeasured.positiveFromWithExtras_compat,BinaryNestedFirstDescriptorMeasured.positiveWithExtras_compat,BinaryNestedFirstDescriptorMeasured.fromParametersWithExtras_compat,BinaryNestedFirstDescriptorMeasured.descriptorWithExtras_compat]
  try { split_ifs <;> rfl }

theorem prepare_data (input : Input) (length : SignedWord) :
    (prepare input length).1.1 = (BinaryNestedFamilyLifetime.inputWithTrace input length).1 := by
  simp only [prepare_record,inputFrom,BinaryNestedFamilyLifetime.inputWithTrace,BinaryNestedParameterMeasured.prepareAt_data]

def inputPrice (s : ℕ) : ℕ := BinaryNestedParameterMeasured.workEnvelope 9 s+8
def inputEnvelope (s : ℕ) : ℕ := BinaryNestedParameterMeasured.envelope 9 s 128 10+64

theorem inputFrom_bounds (input : Input) (length : SignedWord) (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ)
    (P U : ℕ) (h : parameters.2 ≤ P ∧ usage parameters.1.2 ≤ U) :
    (inputFrom input length parameters).2 ≤ P+8 ∧ usage (inputFrom input length parameters).1.2 ≤ U+64 := by
  have hw := wrap_usage 32 2 [parameters.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change parameters.2+8 ≤ _ ∧ usage (wrap 32 2 [parameters.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem prepare_bounds (input : Input) (length : SignedWord) (hC : input.Canonical) (hL : CanonicalWord length)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hLength : RationalHeight (value length) s) :
    (prepare input length).2 ≤ inputPrice s ∧ usage (prepare input length).1.2 ≤ inputEnvelope s := by
  have h := inputFrom_bounds input length (BinaryNestedParameterMeasured.prepareAt input length) _ _
    (BinaryNestedParameterMeasured.prepareAt_bounds input length hC hL s hs hH hLength)
  simp only [prepare_record]
  unfold inputPrice inputEnvelope
  with_reducible exact h

def collect (family : (Input × Trace) × ℕ) (location : (SignedWord × Trace) × ℕ)
    (descriptor : (Segment × Trace) × ℕ) : (Segment × Trace) × ℕ :=
  ((descriptor.1.1,wrap 40 3 [family.1.2,location.1.2,descriptor.1.2]),family.2+location.2+descriptor.2+12)

set_option cleanup.letToHave false in
def fromFamilyWithExtras (family : (Input × Trace) × ℕ) (K : ℕ) (bits : BinaryScalarTape K) : ((Segment × Trace) × ℕ) × ℕ :=
  let location := BinaryNestedFirstLocationMeasured.locationWithExtras family.1.1 K bits
  let descriptor := BinaryNestedFirstDescriptorMeasured.descriptorWithExtras family.1.1 location.1.1.1
  (collect family location.1 descriptor.1,location.2+descriptor.2)

def fromFamily (family : (Input × Trace) × ℕ) (K : ℕ) (bits : BinaryScalarTape K) : (Segment × Trace) × ℕ :=
  (fromFamilyWithExtras family K bits).1

theorem fromFamilyWithExtras_compat (family : (Input × Trace) × ℕ) (K : ℕ) (bits : BinaryScalarTape K) :
    (fromFamilyWithExtras family K bits).1 = fromFamily family K bits := rfl

theorem fromFamily_record (family : (Input × Trace) × ℕ) (K : ℕ) (bits : BinaryScalarTape K) :
    fromFamily family K bits =
  let location := BinaryNestedFirstLocationMeasured.location family.1.1 K bits
  let descriptor := BinaryNestedFirstDescriptorMeasured.descriptor family.1.1 location.1.1
  collect family location descriptor := by
  simp only [fromFamily,fromFamilyWithExtras,BinaryNestedParameterMeasured.runProgramsWithExtras_compat,BinaryNestedParameterMeasured.prepareAtWithExtras_compat,BinaryNestedParameterMeasured.prepareWithExtras_compat,BinaryNestedParameterMeasured.geometryWithExtras_compat,BinaryNestedFirstLocationMeasured.locationWithExtras_compat,BinaryNestedFirstDescriptorMeasured.positiveFromWithExtras_compat,BinaryNestedFirstDescriptorMeasured.positiveWithExtras_compat,BinaryNestedFirstDescriptorMeasured.fromParametersWithExtras_compat,BinaryNestedFirstDescriptorMeasured.descriptorWithExtras_compat,prepareWithExtras_compat]
  try { split_ifs <;> rfl }

set_option cleanup.letToHave false in
def lotteryWithExtras (input : Input) (length : SignedWord) (K : ℕ) (bits : BinaryScalarTape K) : ((Segment × Trace) × ℕ) × ℕ :=
  let family := prepareWithExtras input length
  let produced := fromFamilyWithExtras family.1 K bits
  (produced.1,family.2+produced.2)

def lottery (input : Input) (length : SignedWord) (K : ℕ) (bits : BinaryScalarTape K) : (Segment × Trace) × ℕ :=
  (lotteryWithExtras input length K bits).1

theorem lotteryWithExtras_compat (input : Input) (length : SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    (lotteryWithExtras input length K bits).1 = lottery input length K bits := rfl

theorem lottery_record (input : Input) (length : SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    lottery input length K bits =
  fromFamily (prepare input length) K bits := by
  simp only [lottery,lotteryWithExtras,BinaryNestedParameterMeasured.runProgramsWithExtras_compat,BinaryNestedParameterMeasured.prepareAtWithExtras_compat,BinaryNestedParameterMeasured.prepareWithExtras_compat,BinaryNestedParameterMeasured.geometryWithExtras_compat,BinaryNestedFirstLocationMeasured.locationWithExtras_compat,BinaryNestedFirstDescriptorMeasured.positiveFromWithExtras_compat,BinaryNestedFirstDescriptorMeasured.positiveWithExtras_compat,BinaryNestedFirstDescriptorMeasured.fromParametersWithExtras_compat,BinaryNestedFirstDescriptorMeasured.descriptorWithExtras_compat,prepareWithExtras_compat,fromFamilyWithExtras_compat]
  try { split_ifs <;> rfl }

theorem lottery_data (input : Input) (length : SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    (lottery input length K bits).1.1 = (BinaryNestedFamilyLifetime.lotteryWithTrace input length K bits).1 := by
  simp only [lottery_record,fromFamily_record,collect,BinaryNestedFamilyLifetime.lotteryWithTrace,prepare_data,
    BinaryNestedFirstLocationMeasured.location_data,BinaryNestedFirstDescriptorMeasured.descriptor_data]

def workEnvelope (s K : ℕ) : ℕ := inputPrice s+
  BinaryNestedFirstLocationMeasured.workEnvelope (expressionHeightBudget s 16) K+
  BinaryNestedFirstDescriptorMeasured.workEnvelope (expressionHeightBudget (max (expressionHeightBudget s 16) (K+2)) 16)+12

def envelope (s K : ℕ) : ℕ := inputEnvelope s+
  BinaryNestedFirstLocationMeasured.envelope (expressionHeightBudget s 16) K+
  BinaryNestedFirstDescriptorMeasured.envelope (expressionHeightBudget (max (expressionHeightBudget s 16) (K+2)) 16)+64

theorem collect_bounds (family : (Input × Trace) × ℕ) (location : (SignedWord × Trace) × ℕ)
    (descriptor : (Segment × Trace) × ℕ) (G L D B U F : ℕ)
    (hf : family.2 ≤ G ∧ usage family.1.2 ≤ B) (hl : location.2 ≤ L ∧ usage location.1.2 ≤ U)
    (hd : descriptor.2 ≤ D ∧ usage descriptor.1.2 ≤ F) :
    (collect family location descriptor).2 ≤ G+L+D+12 ∧ usage (collect family location descriptor).1.2 ≤ B+U+F+64 := by
  have hw := wrap_usage 40 3 [family.1.2,location.1.2,descriptor.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change family.2+location.2+descriptor.2+12 ≤ _ ∧ usage (wrap 40 3 [family.1.2,location.1.2,descriptor.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem fromFamily_bounds (family : (Input × Trace) × ℕ) (hC : family.1.1.Canonical)
    (H : ℕ) (hH : 3 ≤ H) (hHeight : BinaryNestedParameterWork.InputHeight family.1.1 H)
    (K : ℕ) (bits : BinaryScalarTape K) (G U : ℕ) (hFamily : family.2 ≤ G ∧ usage family.1.2 ≤ U) :
    (fromFamily family K bits).2 ≤ G+BinaryNestedFirstLocationMeasured.workEnvelope H K+
      BinaryNestedFirstDescriptorMeasured.workEnvelope (expressionHeightBudget (max H (K+2)) 16)+12 ∧
    usage (fromFamily family K bits).1.2 ≤ U+BinaryNestedFirstLocationMeasured.envelope H K+
      BinaryNestedFirstDescriptorMeasured.envelope (expressionHeightBudget (max H (K+2)) 16)+64 := by
  let location := BinaryNestedFirstLocationMeasured.location family.1.1 K bits
  let descriptor := BinaryNestedFirstDescriptorMeasured.descriptor family.1.1 location.1.1
  let T := expressionHeightBudget (max H (K+2)) 16
  have hLocation := BinaryNestedFirstLocationMeasured.location_bounds family.1.1 hC H hH hHeight K bits
  have hLocationState := (BinaryNestedFirstLocationMeasured.location_data family.1.1 K bits).trans
    (BinaryNestedFirstLocationLifetime.locationWithTrace_erasure family.1.1 hC K bits)
  have hLC : CanonicalWord location.1.1 := by rw [hLocationState]; exact BinaryNestedFirstConditional.midpointLocation_canonical family.1.1 hC K bits
  have hLH := BinaryNestedFirstLocationMeasured.location_height family.1.1 hC H hH hHeight K bits
  have hHT : H ≤ T := (le_max_left H (K+2)).trans (expressionHeightBudget_ge_input _ 16)
  have hDescriptor := BinaryNestedFirstDescriptorMeasured.descriptor_bounds family.1.1 location.1.1 hC hLC T (hH.trans hHT)
    (BinaryFactoryHeight.InputHeight.mono hHeight hHT) hLH
  have hResult := collect_bounds family location descriptor _ _ _ _ _ _ hFamily hLocation hDescriptor
  simp only [fromFamily_record]
  simpa only [location,descriptor,T] using hResult

theorem lottery_bounds (input : Input) (length : SignedWord) (hC : input.Canonical) (hL : CanonicalWord length)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hLength : RationalHeight (value length) s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (lottery input length K bits).2 ≤ workEnvelope s K ∧ usage (lottery input length K bits).1.2 ≤ envelope s K := by
  let family := prepare input length
  have hState := (prepare_data input length).trans (BinaryNestedFamilyLifetime.inputWithTrace_erasure input length hC hL)
  have hFC : family.1.1.Canonical := by rw [hState]; exact BinaryNestedComponents.familyInput_canonical input length hC hL
  have hFH : BinaryNestedParameterWork.InputHeight family.1.1 (expressionHeightBudget s 16) := by
    rw [hState]; exact BinaryNestedFamilyFactoryWork.family_input_height input length hC hL s hs hH hLength
  have hResult := fromFamily_bounds family hFC _ (hs.trans (expressionHeightBudget_ge_input s 16)) hFH K bits _ _
    (prepare_bounds input length hC hL s hs hH hLength)
  simp only [lottery_record]
  unfold workEnvelope envelope
  with_reducible exact hResult

def selected (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :=
  lottery input (parameters.read 6) K bits

theorem selected_data (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    (selected input parameters K bits).1.1 = (BinaryNestedFamilyLifetime.selectedWithTrace input parameters K bits).1 := by
  unfold selected BinaryNestedFamilyLifetime.selectedWithTrace
  with_reducible exact lottery_data input (parameters.read 6) K bits

theorem selected_bounds (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (selected input parameters K bits).2 ≤ workEnvelope (expressionHeightBudget s 16) K ∧
      usage (selected input parameters K bits).1.2 ≤ envelope (expressionHeightBudget s 16) K := by
  have hMirror : parameters.read 6 = BinaryNestedComponents.mirror input := by rw [hParameters]; rfl
  unfold selected
  rw [hMirror]
  have hResult := lottery_bounds input (BinaryNestedComponents.mirror input) hC (BinaryNestedComponents.mirror_canonical input hC)
    _ (hs.trans (expressionHeightBudget_ge_input s 16))
    (BinaryFactoryHeight.InputHeight.mono hH (expressionHeightBudget_ge_input s 16))
    (BinaryNestedRemainingFactoryWork.mirror_height input hC s hs hH) K bits
  with_reducible exact hResult

theorem all_prefix (input : Input) (length : SignedWord) (hC : input.Canonical) (hL : CanonicalWord length)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hLength : RationalHeight (value length) s)
    (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (lottery input length K bits).1.2 steps ≤ borrowed+envelope s K ∧
      framePeak ((lottery input length K bits).1.2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (lottery_bounds input length hC hL s hs hH hLength K bits).2 borrowed steps

end Blotto.BinaryNestedFamilyMeasured
