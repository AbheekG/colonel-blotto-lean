import Blotto.BinaryPRGHeapLowerSourceMeasured
import Blotto.BinaryReflectedPreparationMeasured
import Blotto.BinaryReflectedLowerLifetime

/-! Measured reflected preparation feeds the actual deterministic physical
lower resource producer. The returned cache and completed state are retained
for terminal construction. Source-component work and every-prefix storage are
bounded from original six-field heights, within the physical source scope. -/
namespace Blotto.BinaryReflectedLowerMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryReflectedPreparationLifetime BinaryReflectedFourSetup
open BinaryPRGWordControllerBooleanResourceThreeBridge
set_option maxHeartbeats 1500000

def fromPrepared {input : BinaryFourParameters.Input} (prepared : Prepared input) :
    (BinaryThreeResourcePair.Certified (prepare input).capacity × Trace) × ℕ :=
  let lower := BinaryPRGHeapLowerSourceMeasured.native prepared.capacity prepared.system.initial
    prepared.capacity_canonical prepared.canonical.2.2.2
  let state := generalCertified_toThree lower.1.1
  let transported : BinaryThreeResourcePair.Certified (prepare input).capacity := prepared.capacity_source ▸ state
  ((transported,wrap 16 2 [lower.1.2]),lower.2+4)

theorem fromPrepared_erases {input : BinaryFourParameters.Input} (prepared : Prepared input) :
    (fromPrepared prepared).1 = BinaryReflectedLowerLifetime.fromPreparedWithTrace prepared := by
  simp only [fromPrepared,BinaryReflectedLowerLifetime.fromPreparedWithTrace,
    BinaryPRGHeapLowerSourceMeasured.native_erases]

theorem fromPrepared_data (input : BinaryFourParameters.Input) (hC : input.Canonical) (prepared : Prepared input) :
    (fromPrepared prepared).1.1 = BinaryResourceFallback.setup input hC := by
  rw [fromPrepared_erases]
  exact BinaryReflectedLowerLifetime.fromPreparedWithTrace_erasure input hC prepared

theorem fromPrepared_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (prepared : Prepared input) :
    (fromPrepared prepared).2 ≤ BinaryPRGHeapLowerSourceMeasured.workEnvelope (expressionHeightBudget s 15)+4 ∧
      usage (fromPrepared prepared).1.2 ≤ BinaryPRGHeapLowerSourceBound.envelope (expressionHeightBudget s 15)+20 := by
  have hCap : ∀ j,RationalHeight (value (prepared.capacity.read j)) (expressionHeightBudget s 15) := by
    rw [prepared.capacity_source]
    exact BinaryReflectedResourceWork.capacity_height input source hC hR hCase s hs hH
  have hInitial : ∀ j,RationalHeight (value (prepared.system.initial.read j)) (expressionHeightBudget s 15) := by
    rw [prepared.system_correct]
    exact BinaryReflectedResourceWork.initial_resource_height input source hC hR hCase s hs hH
  constructor
  · exact Nat.add_le_add_right (BinaryPRGHeapLowerSourceMeasured.native_work _
      (hs.trans (expressionHeightBudget_ge_input s 15)) prepared.capacity prepared.system.initial
      prepared.capacity_canonical prepared.canonical.2.2.2 hCap hInitial) 4
  · rw [fromPrepared_erases]
    exact BinaryReflectedLowerLifetime.fromPreparedWithTrace_usage input source hC hR hCase s hs hH prepared

def join {input : BinaryFourParameters.Input} (prepared : (Prepared input × Trace) × ℕ)
    (lower : (BinaryThreeResourcePair.Certified (prepare input).capacity × Trace) × ℕ) :
    ((Prepared input × BinaryThreeResourcePair.Certified (prepare input).capacity) × Trace) × ℕ :=
  (((prepared.1.1,lower.1.1),wrap 32 2 [prepared.1.2,lower.1.2]),prepared.2+lower.2+8)

def run (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    ((Prepared input × BinaryThreeResourcePair.Certified (prepare input).capacity) × Trace) × ℕ :=
  let prepared := BinaryReflectedPreparationMeasured.prepare input hC
  join prepared (fromPrepared prepared.1.1)

theorem run_state (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (run input hC).1.1.2 = BinaryResourceFallback.setup input hC :=
  fromPrepared_data input hC _

theorem run_data (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (run input hC).1.1 = (BinaryReflectedLowerLifetime.runWithTrace input hC).1 := by
  apply Prod.ext
  · exact BinaryReflectedPreparationMeasured.prepared_unique _ _
  · exact (run_state input hC).trans (BinaryReflectedLowerLifetime.runWithTrace_erasure input hC).symm

def workEnvelope (s : ℕ) : ℕ := BinaryReflectedPreparationMeasured.workEnvelope s+
  BinaryPRGHeapLowerSourceMeasured.workEnvelope (expressionHeightBudget s 15)+12

def envelope (s : ℕ) : ℕ := BinaryReflectedPreparationMeasured.envelope s+
  BinaryPRGHeapLowerSourceBound.envelope (expressionHeightBudget s 15)+84

theorem join_bounds {input : BinaryFourParameters.Input} (prepared : (Prepared input × Trace) × ℕ)
    (lower : (BinaryThreeResourcePair.Certified (prepare input).capacity × Trace) × ℕ) (P L U V : ℕ)
    (hP : prepared.2 ≤ P ∧ usage prepared.1.2 ≤ U) (hL : lower.2 ≤ L+4 ∧ usage lower.1.2 ≤ V+20) :
    (join prepared lower).2 ≤ P+L+12 ∧ usage (join prepared lower).1.2 ≤ U+V+84 := by
  have hw := wrap_usage 32 2 [prepared.1.2,lower.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change prepared.2+lower.2+8 ≤ _ ∧ usage (wrap 32 2 [prepared.1.2,lower.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem run_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (run input hC).2 ≤ workEnvelope s ∧ usage (run input hC).1.2 ≤ envelope s := by
  let prepared := BinaryReflectedPreparationMeasured.prepare input hC
  let lower := fromPrepared prepared.1.1
  have hP := BinaryReflectedPreparationMeasured.prepare_bounds input source hC hR hCase s hs hH
  have hL := fromPrepared_bounds input source hC hR hCase s hs hH prepared.1.1
  have hResult := join_bounds prepared lower _ _ _ _ hP hL
  unfold run workEnvelope envelope
  with_reducible exact hResult

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (borrowed steps : ℕ) :
    retainedHeap borrowed (run input hC).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((run input hC).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds input source hC hR hCase s hs hH).2 borrowed steps

end Blotto.BinaryReflectedLowerMeasured
