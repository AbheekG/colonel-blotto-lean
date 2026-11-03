import Blotto.BinaryReflectedPreparationMeasured
import Blotto.BinaryReflectedNativeFused
import Blotto.BinaryPRGHeapReflectedLifetime

/-! The returned measured setup feeds the existing traced physical resource
source with its joined work field. Its current physical-source charge and full
trace are retained, not replaced by a native machine-cost assertion. -/
namespace Blotto.BinaryReflectedResourceMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryReflectedFourSetup BinaryPRGHeapTraceUsage BinaryReflectedPreparationLifetime
open BinaryPRGWordControllerBooleanResourceThreeBridge
set_option autoImplicit false
set_option maxHeartbeats 700000

def draw (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input} (prepared : Prepared input)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerThreeResource.Result seed (BinaryReflectedFourSetup.prepare input).capacity × Trace) × ℕ :=
  let drawn := BinaryReflectedNativeFused.native seed prepared.capacity prepared.system.initial
    prepared.capacity_canonical prepared.canonical.2.2.2 pc hp
  let converted : BinaryPRGWordControllerThreeResource.Result seed prepared.capacity :=
    (drawn.1.1.1.map generalCertified_toThree,drawn.1.1.2)
  ((BinaryPRGHeapReflectedLifetime.transport seed prepared converted,wrap 16 2 [drawn.1.2]),drawn.2+4)

theorem draw_erases (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input} (prepared : Prepared input)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (draw seed prepared pc hp).1 =
      (BinaryPRGHeapReflectedLifetime.transport seed prepared (BinaryPRGHeapReflectedLifetime.drawPrepared seed prepared pc hp).1,
        (BinaryPRGHeapReflectedLifetime.drawPrepared seed prepared pc hp).2) := by
  simp only [draw,BinaryReflectedNativeFused.native_previous,BinaryPRGHeapReflectedLifetime.drawPrepared,BinaryPRGHeapNativeLifetime.nativeWithTraceAndWork_erases]

theorem draw_data (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (prepared : Prepared input) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (draw seed prepared pc hp).1.1 = BinaryPRGWordControllerThreeResource.setupIndexed seed input hC pc hp := by
  rw [draw_erases]
  exact BinaryPRGHeapReflectedLifetime.drawPrepared_erasure seed input hC prepared pc hp

theorem draw_work (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input} (prepared : Prepared input)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (draw seed prepared pc hp).2 =
      (BinaryPRGHeapResourceThreeSource.sourceRun seed prepared.capacity prepared.system.initial
        prepared.capacity_canonical prepared.canonical.2.2.2 pc hp).2 := by
  simp only [draw,BinaryReflectedNativeFused.native_previous,BinaryPRGHeapResourceThreeSource.sourceRun,BinaryPRGHeapNativeLifetime.nativeWithTraceAndWork_charge]

theorem draw_bounds (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (prepared : Prepared input)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (draw seed prepared pc hp).2 ≤ BinaryPRGHeapResourceThreeSource.bound (expressionHeightBudget s 15) seed.width seed.cap.value ∧
      usage (draw seed prepared pc hp).1.2 ≤ BinaryPRGHeapThreeNativeLifetimeBound.envelope (expressionHeightBudget s 15) seed.width seed.cap.value+20 := by
  have hCap : ∀ j,RationalHeight (value (prepared.capacity.read j)) (expressionHeightBudget s 15) := by
    rw [prepared.capacity_source]
    exact BinaryReflectedResourceWork.capacity_height input source hC hR hCase s hs hH
  have hInitial : ∀ j,RationalHeight (value (prepared.system.initial.read j)) (expressionHeightBudget s 15) := by
    rw [prepared.system_correct]
    exact BinaryReflectedResourceWork.initial_resource_height input source hC hR hCase s hs hH
  constructor
  · rw [draw_work]
    exact BinaryPRGHeapResourceThreeSource.sourceRun_bound _ (hs.trans (expressionHeightBudget_ge_input s 15)) seed
      prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2 hCap hInitial pc hp
  · rw [draw_erases]
    exact BinaryPRGHeapReflectedLifetime.drawPrepared_usage seed input source hC hR hCase s hs hH prepared pc hp

def join (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input}
    (prepared : (Prepared input × Trace) × ℕ)
    (drawn : (BinaryPRGWordControllerThreeResource.Result seed (BinaryReflectedFourSetup.prepare input).capacity × Trace) × ℕ) :
    ((Prepared input × BinaryPRGWordControllerThreeResource.Result seed (BinaryReflectedFourSetup.prepare input).capacity) × Trace) × ℕ :=
  (((prepared.1.1,drawn.1.1),wrap 32 2 [prepared.1.2,drawn.1.2]),prepared.2+drawn.2+8)

set_option cleanup.letToHave false in
def runWithExtras (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : (((Prepared input × BinaryPRGWordControllerThreeResource.Result seed (BinaryReflectedFourSetup.prepare input).capacity) × Trace) × ℕ) × ℕ :=
  let prepared := BinaryReflectedPreparationMeasured.prepareWithExtras input hC
  let drawn := draw seed prepared.1.1.1 pc hp
  (join seed prepared.1 drawn,prepared.2)

def run (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((Prepared input × BinaryPRGWordControllerThreeResource.Result seed (BinaryReflectedFourSetup.prepare input).capacity) × Trace) × ℕ :=
  (runWithExtras seed input hC pc hp).1

theorem runWithExtras_compat (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runWithExtras seed input hC pc hp).1 = run seed input hC pc hp := rfl

theorem run_record (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    run seed input hC pc hp =
  let prepared := BinaryReflectedPreparationMeasured.prepare input hC
  let drawn := draw seed prepared.1.1 pc hp
  join seed prepared drawn := by
  simp only [run,runWithExtras,BinaryReflectedPreparationMeasured.fromSystemWithExtras_compat,BinaryReflectedPreparationMeasured.fromParametersWithExtras_compat,BinaryReflectedPreparationMeasured.prepareWithExtras_compat]

theorem run_eq (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : run seed input hC pc hp =
      let prepared := BinaryReflectedPreparationMeasured.prepare input hC
      join seed prepared (draw seed prepared.1.1 pc hp) := by
  simp only [run_record]

theorem run_resource (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (run seed input hC pc hp).1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed seed input hC pc hp :=
  draw_data seed input hC _ pc hp

theorem run_data (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (run seed input hC pc hp).1.1 = (BinaryPRGHeapReflectedLifetime.runWithTrace seed input hC pc hp).1 := by
  apply Prod.ext
  · exact BinaryReflectedPreparationMeasured.prepared_unique _ _
  · exact (run_resource seed input hC pc hp).trans
      ((BinaryPRGHeapReflectedLifetime.runWithTrace_erasure seed input hC pc hp).trans
        (BinaryPRGHeapReflectedSetup.run_erasure seed input hC pc hp)).symm

def workEnvelope (s i cap : ℕ) : ℕ := BinaryReflectedPreparationMeasured.workEnvelope s+
  BinaryPRGHeapResourceThreeSource.bound (expressionHeightBudget s 15) i cap+8

def envelope (s i cap : ℕ) : ℕ := BinaryReflectedPreparationMeasured.envelope s+
  BinaryPRGHeapThreeNativeLifetimeBound.envelope (expressionHeightBudget s 15) i cap+84

theorem join_bounds (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input}
    (prepared : (Prepared input × Trace) × ℕ)
    (drawn : (BinaryPRGWordControllerThreeResource.Result seed (BinaryReflectedFourSetup.prepare input).capacity × Trace) × ℕ)
    (P D B C : ℕ) (hp : prepared.2 ≤ P ∧ usage prepared.1.2 ≤ B) (hd : drawn.2 ≤ D ∧ usage drawn.1.2 ≤ C+20) :
    (join seed prepared drawn).2 ≤ P+D+8 ∧ usage (join seed prepared drawn).1.2 ≤ B+C+84 := by
  have hw := wrap_usage 32 2 [prepared.1.2,drawn.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change prepared.2+drawn.2+8 ≤ _ ∧ usage (wrap 32 2 [prepared.1.2,drawn.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem run_bounds (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (run seed input hC pc hp).2 ≤ workEnvelope s seed.width seed.cap.value ∧
      usage (run seed input hC pc hp).1.2 ≤ envelope s seed.width seed.cap.value := by
  let prepared := BinaryReflectedPreparationMeasured.prepare input hC
  let drawn := draw seed prepared.1.1 pc hp
  have hP := BinaryReflectedPreparationMeasured.prepare_bounds input source hC hR hCase s hs hH
  have hD := draw_bounds seed input source hC hR hCase s hs hH prepared.1.1 pc hp
  have hResult := join_bounds seed prepared drawn _ _ _ _ hP hD
  rw [run_eq]
  simpa only [prepared,drawn,workEnvelope,envelope] using hResult

theorem run_position (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    pc.value ≤ (run seed input hC pc hp).1.1.2.2.value ∧ (run seed input hC pc hp).1.1.2.2.value ≤ seed.cap.value := by
  rw [run_resource]
  exact BinaryPRGWordControllerThreeResource.setupIndexed_position seed input hC pc hp

theorem all_prefix (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run seed input hC pc hp).1.2 steps ≤ borrowed+envelope s seed.width seed.cap.value ∧
      framePeak ((run seed input hC pc hp).1.2.take steps) ≤ envelope s seed.width seed.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds seed input source hC hR hCase s hs hH pc hp).2 borrowed steps

end Blotto.BinaryReflectedResourceMeasured
