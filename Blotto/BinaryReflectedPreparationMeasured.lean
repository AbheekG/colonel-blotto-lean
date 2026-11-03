import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryFourParametersMeasured
import Blotto.BinaryReflectedSystemMeasured
import Blotto.BinaryReflectedPreparationLifetime

/-! Returned measured parameters feed the measured system and capacity once.
The retained certified record equals its previous value; new source work and
trace bounds follow from original fields. Native realization remains separate. -/
namespace Blotto.BinaryReflectedPreparationMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryReflectedFourSetup BinaryPRGHeapTraceUsage BinaryReflectedPreparationLifetime
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem prepared_unique {input : BinaryFourParameters.Input} (a b : Prepared input) : a = b := by
  cases a with
  | mk pa hpa hpc sa hsa hsc ca hca hcc =>
    cases b with
    | mk pb hpb hpd sb hsb hsd cb hcb hcd =>
      cases hpa
      cases hpb
      cases hsa
      cases hsb
      cases hca
      cases hcb
      rfl

def assemble (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ) (system : (System × Trace) × ℕ)
    (capacity : (FixedArrayTable 3 SignedWord × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (hSystem : system.1.1 = BinaryReflectedFourSetup.prepare input)
    (hCapacity : capacity.1.1 = system.1.1.capacity) : (Prepared input × Trace) × ℕ :=
  ((⟨parameters.1.1,hParameters,
    (by rw [hParameters]; exact BinaryFourParameters.prepare_canonical input hC),
    system.1.1,hSystem,(by rw [hSystem]; exact prepare_canonical input hC),capacity.1.1,hCapacity,
    (by rw [hCapacity,hSystem]; exact capacity_canonical _ (prepare_canonical input hC))⟩,
    wrap 48 4 [parameters.1.2,system.1.2,capacity.1.2]),parameters.2+system.2+capacity.2+16)

theorem system_correct (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord)
    (hC : input.Canonical) (hPC : ∀ j,CanonicalWord (parameters.read j))
    (hParameters : parameters = BinaryFourParameters.prepare input) :
    (BinaryReflectedSystemMeasured.fromParameters input parameters).1.1 = BinaryReflectedFourSetup.prepare input := by
  rw [BinaryReflectedSystemMeasured.fromParameters_data,
    BinaryReflectedSystemLifetime.fromParametersWithTrace_erasure input parameters hC hPC,hParameters]
  rfl

theorem capacity_correct (system : System) (hSC : system.Canonical) :
    (BinaryReflectedSystemMeasured.capacity system).1.1 = system.capacity :=
  (BinaryReflectedSystemMeasured.capacity_data system).trans
    (BinaryReflectedSystemLifetime.capacityWithTrace_erasure system hSC)

set_option cleanup.letToHave false in
def fromSystemWithExtras (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ) (system : (System × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (hSystem : system.1.1 = BinaryReflectedFourSetup.prepare input) : ((Prepared input × Trace) × ℕ) × ℕ :=
  have hSC : system.1.1.Canonical := by rw [hSystem]; exact prepare_canonical input hC
  let capacity := BinaryReflectedSystemMeasured.capacityWithExtras system.1.1
  (assemble input hC parameters system capacity.1 hParameters hSystem
    (by simpa only [capacity,BinaryReflectedSystemMeasured.capacityWithExtras_compat] using capacity_correct system.1.1 hSC),capacity.2)

def fromSystem (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ) (system : (System × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (hSystem : system.1.1 = BinaryReflectedFourSetup.prepare input) : (Prepared input × Trace) × ℕ :=
  (fromSystemWithExtras input hC parameters system hParameters hSystem).1

theorem fromSystemWithExtras_compat (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ) (system : (System × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (hSystem : system.1.1 = BinaryReflectedFourSetup.prepare input) :
    (fromSystemWithExtras input hC parameters system hParameters hSystem).1 = fromSystem input hC parameters system hParameters hSystem := rfl

theorem fromSystem_record (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ) (system : (System × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (hSystem : system.1.1 = BinaryReflectedFourSetup.prepare input) :
    fromSystem input hC parameters system hParameters hSystem =
  have hSC : system.1.1.Canonical := by rw [hSystem]; exact prepare_canonical input hC
  let capacity := BinaryReflectedSystemMeasured.capacity system.1.1
  assemble input hC parameters system capacity hParameters hSystem (capacity_correct system.1.1 hSC) := by
  simp only [fromSystem,fromSystemWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryFourParametersMeasured.prepareWithExtras_compat,BinaryReflectedSystemMeasured.capacityWithExtras_compat,BinaryReflectedSystemMeasured.fromParametersWithExtras_compat]

set_option cleanup.letToHave false in
def fromParametersWithExtras (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input) : ((Prepared input × Trace) × ℕ) × ℕ :=
  have hPC : ∀ j,CanonicalWord (parameters.1.1.read j) := by rw [hParameters]; exact BinaryFourParameters.prepare_canonical input hC
  let system := BinaryReflectedSystemMeasured.fromParametersWithExtras input parameters.1.1
  let produced := fromSystemWithExtras input hC parameters system.1 hParameters
    (by simpa only [system,BinaryReflectedSystemMeasured.fromParametersWithExtras_compat] using system_correct input parameters.1.1 hC hPC hParameters)
  (produced.1,system.2+produced.2)

def fromParameters (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input) : (Prepared input × Trace) × ℕ :=
  (fromParametersWithExtras input hC parameters hParameters).1

theorem fromParametersWithExtras_compat (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input) :
    (fromParametersWithExtras input hC parameters hParameters).1 = fromParameters input hC parameters hParameters := rfl

theorem fromParameters_record (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input) :
    fromParameters input hC parameters hParameters =
  have hPC : ∀ j,CanonicalWord (parameters.1.1.read j) := by rw [hParameters]; exact BinaryFourParameters.prepare_canonical input hC
  let system := BinaryReflectedSystemMeasured.fromParameters input parameters.1.1
  fromSystem input hC parameters system hParameters (system_correct input parameters.1.1 hC hPC hParameters) := by
  simp only [fromParameters,fromParametersWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryFourParametersMeasured.prepareWithExtras_compat,BinaryReflectedSystemMeasured.capacityWithExtras_compat,BinaryReflectedSystemMeasured.fromParametersWithExtras_compat,fromSystemWithExtras_compat]

set_option cleanup.letToHave false in
def prepareWithExtras (input : BinaryFourParameters.Input) (hC : input.Canonical) : ((Prepared input × Trace) × ℕ) × ℕ :=
  let parameters := BinaryFourParametersMeasured.prepareWithExtras input
  let produced := fromParametersWithExtras input hC parameters.1
    (by simpa only [parameters,BinaryFourParametersMeasured.prepareWithExtras_compat] using
      (BinaryFourParametersMeasured.prepare_data input).trans (BinaryReflectedParameterLifetime.prepareWithTrace_erasure input hC))
  (produced.1,parameters.2+produced.2)

def prepare (input : BinaryFourParameters.Input) (hC : input.Canonical) : (Prepared input × Trace) × ℕ :=
  (prepareWithExtras input hC).1

theorem prepareWithExtras_compat (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (prepareWithExtras input hC).1 = prepare input hC := rfl

theorem prepare_record (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    prepare input hC =
  let parameters := BinaryFourParametersMeasured.prepare input
  fromParameters input hC parameters ((BinaryFourParametersMeasured.prepare_data input).trans
    (BinaryReflectedParameterLifetime.prepareWithTrace_erasure input hC)) := by
  simp only [prepare,prepareWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryFourParametersMeasured.prepareWithExtras_compat,BinaryReflectedSystemMeasured.capacityWithExtras_compat,BinaryReflectedSystemMeasured.fromParametersWithExtras_compat,fromSystemWithExtras_compat,fromParametersWithExtras_compat]

theorem prepare_data (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (prepare input hC).1.1 = (BinaryReflectedPreparationLifetime.prepareWithTrace input hC).1 :=
  prepared_unique _ _

def workEnvelope (s : ℕ) : ℕ := BinaryFourParametersMeasured.workEnvelope s+
  BinaryReflectedSystemMeasured.workEnvelope (expressionHeightBudget s 12)+
  BinaryReflectedSystemMeasured.capacityPrice (expressionHeightBudget s 14)+16

def envelope (s : ℕ) : ℕ := BinaryFourParametersMeasured.envelope s+
  BinaryReflectedSystemMeasured.envelope (expressionHeightBudget s 12)+
  BinaryReflectedSystemMeasured.capacityEnvelope (expressionHeightBudget s 14)+64

theorem assemble_bounds (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ) (system : (System × Trace) × ℕ)
    (capacity : (FixedArrayTable 3 SignedWord × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (hSystem : system.1.1 = BinaryReflectedFourSetup.prepare input) (hCapacity : capacity.1.1 = system.1.1.capacity)
    (P S C B F H : ℕ) (hp : parameters.2 ≤ P ∧ usage parameters.1.2 ≤ B)
    (hs : system.2 ≤ S ∧ usage system.1.2 ≤ F) (hc : capacity.2 ≤ C ∧ usage capacity.1.2 ≤ H) :
    (assemble input hC parameters system capacity hParameters hSystem hCapacity).2 ≤ P+S+C+16 ∧
      usage (assemble input hC parameters system capacity hParameters hSystem hCapacity).1.2 ≤ B+F+H+64 := by
  have hw := wrap_usage 48 4 [parameters.1.2,system.1.2,capacity.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change parameters.2+system.2+capacity.2+16 ≤ _ ∧ usage (wrap 48 4 [parameters.1.2,system.1.2,capacity.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem fromSystem_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ) (system : (System × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (hSystem : system.1.1 = BinaryReflectedFourSetup.prepare input)
    (hP : parameters.2 ≤ BinaryFourParametersMeasured.workEnvelope s ∧ usage parameters.1.2 ≤ BinaryFourParametersMeasured.envelope s)
    (hS : system.2 ≤ BinaryReflectedSystemMeasured.workEnvelope (expressionHeightBudget s 12) ∧
      usage system.1.2 ≤ BinaryReflectedSystemMeasured.envelope (expressionHeightBudget s 12)) :
    (fromSystem input hC parameters system hParameters hSystem).2 ≤ workEnvelope s ∧
      usage (fromSystem input hC parameters system hParameters hSystem).1.2 ≤ envelope s := by
  have hSC : system.1.1.Canonical := by rw [hSystem]; exact prepare_canonical input hC
  let capacity := BinaryReflectedSystemMeasured.capacity system.1.1
  have hCE : capacity.1.1 = system.1.1.capacity := capacity_correct system.1.1 hSC
  have hRef := prepare_refines input source hC hR hCase
  have hSourceHeight := hH.reflectedResourceSystem hs hCase
  have hLong : ∀ j,RationalHeight (value (system.1.1.long.read j)) (expressionHeightBudget s 14) := by
    intro j; rw [hSystem,hRef.2.1 j]; exact hSourceHeight.2.1 j
  have hShort : ∀ j,RationalHeight (value (system.1.1.short.read j)) (expressionHeightBudget s 14) := by
    intro j; rw [hSystem,hRef.2.2.1 j]; exact hSourceHeight.2.2.1 j
  have hCap := BinaryReflectedSystemMeasured.capacity_bounds system.1.1 hSC _ hLong hShort
  have hResult := assemble_bounds input hC parameters system capacity hParameters hSystem hCE _ _ _ _ _ _ hP hS hCap
  simp only [fromSystem_record]
  simpa only [capacity,workEnvelope,envelope] using hResult

theorem fromParameters_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (hP : parameters.2 ≤ BinaryFourParametersMeasured.workEnvelope s ∧ usage parameters.1.2 ≤ BinaryFourParametersMeasured.envelope s) :
    (fromParameters input hC parameters hParameters).2 ≤ workEnvelope s ∧
      usage (fromParameters input hC parameters hParameters).1.2 ≤ envelope s := by
  have hPC : ∀ j,CanonicalWord (parameters.1.1.read j) := by rw [hParameters]; exact BinaryFourParameters.prepare_canonical input hC
  let system := BinaryReflectedSystemMeasured.fromParameters input parameters.1.1
  have hSE : system.1.1 = BinaryReflectedFourSetup.prepare input := system_correct input parameters.1.1 hC hPC hParameters
  have hParameterH : ∀ j,RationalHeight (value (parameters.1.1.read j)) (expressionHeightBudget s 12) := by
    intro j; rw [hParameters,BinaryFourParameters.prepare_value input source hC hR j]; exact hH.scalar hs j
  have hLengthH : ∀ j,RationalHeight (value ((originalLengths input).read j)) (expressionHeightBudget s 12) := by
    intro j; rw [originalLengths_value input source hR j]
    exact (hH.originalLengths j).mono (expressionHeightBudget_ge_input s 12)
  have hS := BinaryReflectedSystemMeasured.fromParameters_bounds input parameters.1.1 hC hPC _ hParameterH hLengthH
  have hResult := fromSystem_bounds input source hC hR hCase s hs hH parameters system hParameters hSE hP hS
  simp only [fromParameters_record]
  with_reducible exact hResult

theorem prepare_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (prepare input hC).2 ≤ workEnvelope s ∧ usage (prepare input hC).1.2 ≤ envelope s := by
  have hP := BinaryFourParametersMeasured.prepare_bounds input source hC hR s hs hH
  simp only [prepare_record]
  exact fromParameters_bounds input source hC hR hCase s hs hH _ _ hP

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepare input hC).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((prepare input hC).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepare_bounds input source hC hR hCase s hs hH).2 borrowed steps

end Blotto.BinaryReflectedPreparationMeasured
