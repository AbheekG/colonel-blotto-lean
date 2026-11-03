import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryNestedFirstAssemblyMeasured
import Blotto.BinaryPhysicalPointMeasured
import Blotto.BinaryReflectedEmissionLifetime
import Blotto.BinaryQuadraticPointOutputLifetime

/-! One actual measured physical point feeds three measured original-length
subtractions and measured four-word output packing with final zero. Original
endpoint/length heights derive source work and every-prefix retained bounds. -/
namespace Blotto.BinaryReflectedEmissionMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryLifetimeUsage BinaryReflectedFourSetup
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 1200000

abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def collectRow (differences : (FixedArrayTable 3 SignedWord × Trace) × ℕ) : (FixedArrayTable 4 SignedWord × Trace) × ℕ :=
  let output := BinaryThreeReferenceMeasured.references 4 ![differences.1.1.read 0,differences.1.1.read 1,differences.1.1.read 2,BinaryRationalOpcode.zero]
  ((output.1.1,wrap 32 2 [differences.1.2,output.1.2]),differences.2+output.2+8)

set_option cleanup.letToHave false in
def reflectWithExtras (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) : ((FixedArrayTable 4 SignedWord × Trace) × ℕ) × ℕ :=
  let produced := BinaryLifetimeArrayExtras.build 3 (fun j =>
    BinaryNormalizedCoordinate.opcode .sub ((originalLengths input).read j) (row.read j))
  (collectRow produced.1,produced.2)

def reflect (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) : (FixedArrayTable 4 SignedWord × Trace) × ℕ :=
  (reflectWithExtras input row).1

theorem reflectWithExtras_compat (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord)  :
    (reflectWithExtras input row).1 = reflect input row := rfl

theorem reflect_record (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord)  :
    reflect input row =
  collectRow (BinaryLifetimeArrayMeasured.build 3 (fun j => BinaryPlannedQuadratic.apply .sub ((originalLengths input).read j) (row.read j))) := by
  simp only [reflect,reflectWithExtras,BinaryLifetimeArrayExtras.build_record,
    BinaryNormalizedCoordinate.opcode_record]


theorem reflect_data (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) :
    (reflect input row).1.1 = (BinaryReflectedEmissionLifetime.reflectWithTrace input row).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,reflect_record,collectRow,BinaryReflectedEmissionLifetime.reflectWithTrace,BinaryThreeReferenceMeasured.references_data,
    BinaryLifetimeArrayMeasured.build_data,BinaryLifetimeArray.build_erases,BinaryQuadraticMeasured.apply_erases,
    BinaryNestedResidualLifetime.copyWithTrace_erasure]

def reflectPrice (W : ℕ) : ℕ := 3*BinaryReflectedSystemMeasured.opcodePrice W+3000
def reflectEnvelope (W : ℕ) : ℕ := 4*opcodeEnvelope W+1800

theorem collectRow_bounds (differences : (FixedArrayTable 3 SignedWord × Trace) × ℕ) (P U : ℕ)
    (hd : differences.2 ≤ P ∧ usage differences.1.2 ≤ U) :
    (collectRow differences).2 ≤ P+1616+8 ∧ usage (collectRow differences).1.2 ≤ U+915+64 := by
  let output := BinaryThreeReferenceMeasured.references 4 ![differences.1.1.read 0,differences.1.1.read 1,differences.1.1.read 2,BinaryRationalOpcode.zero]
  have hp : output.2 ≤ 1616 ∧ usage output.1.2 ≤ 915 :=
    ⟨BinaryThreeReferenceMeasured.references_work 4 _,BinaryThreeReferenceMeasured.references_usage 4 _⟩
  have hw := wrap_usage 32 2 [differences.1.2,output.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change differences.2+output.2+8 ≤ _ ∧ usage (wrap 32 2 [differences.1.2,output.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem reflect_bounds (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) (W : ℕ)
    (hLengths : ∀ j,width ((originalLengths input).read j) ≤ W) (hRow : ∀ j,width (row.read j) ≤ W) :
    (reflect input row).2 ≤ reflectPrice W ∧ usage (reflect input row).1.2 ≤ reflectEnvelope W := by
  let produce : Fin 3 → (SignedWord × Trace) × ℕ := fun j => BinaryQuadraticMeasured.apply .sub ((originalLengths input).read j) (row.read j)
  let differences := BinaryLifetimeArrayMeasured.build 3 produce
  have hEach : ∀ j,(produce j).2 ≤ BinaryReflectedSystemMeasured.opcodePrice W ∧ usage (produce j).1.2 ≤ opcodeEnvelope W := by
    intro j
    exact BinaryReflectedSystemMeasured.opcode_bounds .sub ((originalLengths input).read j) (row.read j) W (hLengths j) (hRow j)
  have hw := BinaryLifetimeArrayMeasured.build_work_bound 3 produce _ (fun j => (hEach j).1)
  have hu := BinaryLifetimeArrayMeasured.build_bounds 3 produce (opcodeEnvelope W) (opcodeEnvelope W)
    (by intro j; have h := (hEach j).2; unfold usage at h; omega)
    (by intro j; have h := (hEach j).2; unfold usage at h; omega)
  have hResult := collectRow_bounds differences _ _ ⟨hw,hu⟩
  have hFinal : (collectRow differences).2 ≤ reflectPrice W ∧ usage (collectRow differences).1.2 ≤ reflectEnvelope W :=
    ⟨hResult.1.trans (by unfold reflectPrice; omega),
      hResult.2.trans (by unfold reflectEnvelope BinaryLifetimeArrayMeasured.storageReserve; omega)⟩
  simp only [reflect_record, BinaryPlannedQuadratic.apply_previous]
  exact hFinal

def collect (point : (FixedArrayTable 3 SignedWord × Trace) × ℕ) (output : (FixedArrayTable 4 SignedWord × Trace) × ℕ) :
    (FixedArrayTable 4 SignedWord × Trace) × ℕ :=
  ((output.1.1,wrap 32 2 [point.1.2,output.1.2]),point.2+output.2+8)

set_option cleanup.letToHave false in
def sampleWithExtras (input : BinaryFourParameters.Input) (table : Segment) (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) : ((FixedArrayTable 4 SignedWord × Trace) × ℕ) × ℕ :=
  let point := BinaryPhysicalPointMeasured.sampleWithExtras table slot K scalar
  let emitted := reflectWithExtras input point.1.1.1
  (collect point.1 emitted.1,point.2+emitted.2)

def sample (input : BinaryFourParameters.Input) (table : Segment) (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) :
    (FixedArrayTable 4 SignedWord × Trace) × ℕ :=
  (sampleWithExtras input table slot K scalar).1

theorem sampleWithExtras_compat (input : BinaryFourParameters.Input) (table : Segment) (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K)  :
    (sampleWithExtras input table slot K scalar).1 = sample input table slot K scalar := rfl

theorem sample_record (input : BinaryFourParameters.Input) (table : Segment) (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K)  :
    sample input table slot K scalar =
  let point := BinaryPhysicalPointMeasured.sample table slot K scalar
  collect point (reflect input point.1.1) := by
  simp only [sample,sampleWithExtras,BinaryPhysicalPointMeasured.sampleWithExtras_compat,
    reflectWithExtras_compat]


theorem point_erases (table : Segment) (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) :
    (BinaryPhysicalPointMeasured.sample table slot K scalar).1 = BinaryQuadraticPointLifetime.sampleWithTrace table slot K scalar := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryPhysicalPointMeasured.sample_erases,BinaryQuadraticPointLifetime.sampleWithTrace]

theorem sample_data (input : BinaryFourParameters.Input) (table : Segment) (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) :
    (sample input table slot K scalar).1.1 = (BinaryReflectedEmissionLifetime.sampleWithTrace input table slot K scalar).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,sample_record,collect,BinaryReflectedEmissionLifetime.sampleWithTrace,reflect_data,point_erases]

def widthEnvelope (s K : ℕ) : ℕ := BinaryQuadraticPointOutputLifetime.rowWidth s K
def workEnvelope (s K : ℕ) : ℕ := BinaryPhysicalPointMeasured.price 3 s K+reflectPrice (widthEnvelope s K)+8
def envelope (s K : ℕ) : ℕ := BinaryPhysicalPointLifetime.bound 3 s K+reflectEnvelope (widthEnvelope s K)+64

theorem collect_bounds (point : (FixedArrayTable 3 SignedWord × Trace) × ℕ) (output : (FixedArrayTable 4 SignedWord × Trace) × ℕ)
    (P O U F : ℕ) (hp : point.2 ≤ P ∧ usage point.1.2 ≤ U) (ho : output.2 ≤ O ∧ usage output.1.2 ≤ F) :
    (collect point output).2 ≤ P+O+8 ∧ usage (collect point output).1.2 ≤ U+F+64 := by
  have hw := wrap_usage 32 2 [point.1.2,output.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change point.2+output.2+8 ≤ _ ∧ usage (wrap 32 2 [point.1.2,output.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem sample_bounds (input : BinaryFourParameters.Input) (hC : input.Canonical) (table : Segment) (hTable : table.Canonical)
    (s : ℕ) (hs : 3 ≤ s)
    (hEndpoint : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧ RationalHeight (value ((table.Q.read slot).read j)) s)
    (hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) s)
    (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) :
    (sample input table slot K scalar).2 ≤ workEnvelope s K ∧ usage (sample input table slot K scalar).1.2 ≤ envelope s K := by
  let point := BinaryPhysicalPointMeasured.sample table slot K scalar
  have hPoint : point.2 ≤ BinaryPhysicalPointMeasured.price 3 s K ∧ usage point.1.2 ≤ BinaryPhysicalPointLifetime.bound 3 s K :=
    ⟨BinaryPhysicalPointMeasured.sample_work table hTable s hEndpoint slot K scalar,
      by rw [BinaryPhysicalPointMeasured.sample_erases]; exact BinaryPhysicalPointLifetime.sample_usage table hTable s hs hEndpoint slot K scalar⟩
  have hRow : ∀ j,width (point.1.1.read j) ≤ widthEnvelope s K := by
    rw [point_erases]; exact BinaryQuadraticPointOutputLifetime.point_width table hTable s hs hEndpoint slot K scalar
  have hL : ∀ j,width ((originalLengths input).read j) ≤ widthEnvelope s K := by
    intro j
    have h := (originalLengths_canonical input hC j).2.trans (rationalWordWidth_of_height (hLengths j))
    have hm := (le_max_left s (K+2)).trans (expressionHeightBudget_ge_input _ 3)
    unfold widthEnvelope BinaryQuadraticPointOutputLifetime.rowWidth; omega
  have hReflect := reflect_bounds input point.1.1 _ hL hRow
  have hResult := collect_bounds point (reflect input point.1.1) _ _ _ _ hPoint hReflect
  rw [sample_record]
  unfold workEnvelope envelope
  with_reducible exact hResult

theorem all_prefix (input : BinaryFourParameters.Input) (hC : input.Canonical) (table : Segment) (hTable : table.Canonical)
    (s : ℕ) (hs : 3 ≤ s)
    (hEndpoint : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧ RationalHeight (value ((table.Q.read slot).read j)) s)
    (hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) s)
    (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (sample input table slot K scalar).1.2 steps ≤ borrowed+envelope s K ∧ framePeak ((sample input table slot K scalar).1.2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (sample_bounds input hC table hTable s hs hEndpoint hLengths slot K scalar).2 borrowed steps

end Blotto.BinaryReflectedEmissionMeasured
