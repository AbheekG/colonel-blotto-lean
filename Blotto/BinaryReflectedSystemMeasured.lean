import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryPlannedQuadratic
import Blotto.BinarySmallUniformPreparationMeasured
import Blotto.BinaryReflectedSystemLifetime

/-! Actual measured length packing, seven products and returned short/initial
arrays build the reflected system. Three measured subtractions build capacity.
Source-field bounds cover enlarged traces; native model realization is separate. -/
namespace Blotto.BinaryReflectedSystemMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryReflectedFourSetup BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 600000

def lengths (input : BinaryFourParameters.Input) : (FixedArrayTable 3 SignedWord × Trace) × ℕ :=
  BinaryThreeReferenceMeasured.references 3 ![input.u,input.v,input.w]

theorem lengths_data (input : BinaryFourParameters.Input) : (lengths input).1.1 = originalLengths input :=
  BinaryThreeReferenceMeasured.references_data _ _

def assemble (M : SignedWord) (long : (FixedArrayTable 3 SignedWord × Trace) × ℕ)
    (scale : (SignedWord × Trace) × ℕ) (short initial : (FixedArrayTable 3 SignedWord × Trace) × ℕ) :
    (System × Trace) × ℕ :=
  ((⟨M,long.1.1,short.1.1,initial.1.1⟩,wrap 192 8 [long.1.2,scale.1.2,short.1.2,initial.1.2]),
    long.2+scale.2+short.2+initial.2+16)

set_option cleanup.letToHave false in
def fromParametersWithExtras (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) : ((System × Trace) × ℕ) × ℕ :=
  let long := lengths input
  let scale := BinaryNormalizedCoordinate.opcode .mul (parameters.read 6) (parameters.read 5)
  let short := BinaryLifetimeArrayExtras.build 3
    (fun j => BinaryNormalizedCoordinate.opcode .mul (parameters.read 4) (long.1.1.read j))
  let initial := BinaryLifetimeArrayExtras.build 3
    (fun j => BinaryNormalizedCoordinate.opcode .mul scale.1.1.1 (long.1.1.read j))
  (assemble (parameters.read 7) long scale.1 short.1 initial.1,scale.2+short.2+initial.2)

def fromParameters (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) : (System × Trace) × ℕ :=
  (fromParametersWithExtras input parameters).1

theorem fromParametersWithExtras_compat (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) :
    (fromParametersWithExtras input parameters).1 = fromParameters input parameters := rfl

theorem fromParameters_record (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) :
    fromParameters input parameters =
  let long := lengths input
  let scale := BinaryPlannedQuadratic.apply .mul (parameters.read 6) (parameters.read 5)
  let short := BinaryLifetimeArrayMeasured.build 3
    (fun j => BinaryPlannedQuadratic.apply .mul (parameters.read 4) (long.1.1.read j))
  let initial := BinaryLifetimeArrayMeasured.build 3
    (fun j => BinaryPlannedQuadratic.apply .mul scale.1.1 (long.1.1.read j))
  assemble (parameters.read 7) long scale short initial := by
  simp only [fromParameters,fromParametersWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record]

theorem fromParameters_eq (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) :
    fromParameters input parameters =
      let long := lengths input
      let scale := BinaryQuadraticMeasured.apply .mul (parameters.read 6) (parameters.read 5)
      assemble (parameters.read 7) long scale
        (BinaryLifetimeArrayMeasured.build 3 (fun j => BinaryQuadraticMeasured.apply .mul (parameters.read 4) (long.1.1.read j)))
        (BinaryLifetimeArrayMeasured.build 3 (fun j => BinaryQuadraticMeasured.apply .mul scale.1.1 (long.1.1.read j))) := by
  simp only [fromParameters_record, BinaryPlannedQuadratic.apply_previous]

theorem fromParameters_data (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) :
    (fromParameters input parameters).1.1 = (BinaryReflectedSystemLifetime.fromParametersWithTrace input parameters).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,fromParameters_record,assemble,BinaryReflectedSystemLifetime.fromParametersWithTrace,lengths_data,
    BinaryLifetimeArrayMeasured.build_data,BinaryQuadraticMeasured.apply_erases]

def opcodePrice (W : ℕ) : ℕ := 11000*(W+1)^2
def workEnvelope (t : ℕ) : ℕ := 7*opcodePrice (4*t+1)+4000
def envelope (t : ℕ) : ℕ := 9*opcodeEnvelope (4*t+1)+5000

theorem opcode_bounds (op : RealArithmeticOp) (a b : SignedWord) (W : ℕ)
    (ha : width a ≤ W) (hb : width b ≤ W) :
    (BinaryQuadraticMeasured.apply op a b).2 ≤ opcodePrice W ∧
      usage (BinaryQuadraticMeasured.apply op a b).1.2 ≤ opcodeEnvelope W := by
  refine ⟨BinaryFourGuardMeasured.opcode_work op a b W ha hb,?_⟩
  rw [BinaryQuadraticMeasured.apply_erases]
  exact opcode_usage op a b W ha hb

theorem assemble_bounds (M : SignedWord) (long : (FixedArrayTable 3 SignedWord × Trace) × ℕ)
    (scale : (SignedWord × Trace) × ℕ) (short initial : (FixedArrayTable 3 SignedWord × Trace) × ℕ)
    (P U : ℕ) (hl : long.2 ≤ 1036 ∧ usage long.1.2 ≤ 617)
    (hs : scale.2 ≤ P ∧ usage scale.1.2 ≤ U)
    (ht : short.2 ≤ 3*P+1024 ∧ usage short.1.2 ≤ 4*U+592)
    (hi : initial.2 ≤ 3*P+1024 ∧ usage initial.1.2 ≤ 4*U+592) :
    (assemble M long scale short initial).2 ≤ 7*P+4000 ∧
      usage (assemble M long scale short initial).1.2 ≤ 9*U+5000 := by
  have hw := wrap_usage 192 8 [long.1.2,scale.1.2,short.1.2,initial.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change long.2+scale.2+short.2+initial.2+16 ≤ _ ∧ usage (wrap 192 8 [long.1.2,scale.1.2,short.1.2,initial.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem fromParameters_bounds (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord)
    (hC : input.Canonical) (hP : ∀ j,CanonicalWord (parameters.read j)) (t : ℕ)
    (hParameters : ∀ j,RationalHeight (value (parameters.read j)) t)
    (hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) t) :
    (fromParameters input parameters).2 ≤ workEnvelope t ∧ usage (fromParameters input parameters).1.2 ≤ envelope t := by
  let long := lengths input
  let scale := BinaryQuadraticMeasured.apply .mul (parameters.read 6) (parameters.read 5)
  let short := BinaryLifetimeArrayMeasured.build 3 (fun j => BinaryQuadraticMeasured.apply .mul (parameters.read 4) (long.1.1.read j))
  let initial := BinaryLifetimeArrayMeasured.build 3 (fun j => BinaryQuadraticMeasured.apply .mul scale.1.1 (long.1.1.read j))
  let W := 4*t+1
  have hpWidth : ∀ j,width (parameters.read j) ≤ W := by
    intro j
    have h := (hP j).2.trans (rationalWordWidth_of_height (hParameters j))
    dsimp only [W]; omega
  have hlWidth : ∀ j,width (long.1.1.read j) ≤ W := by
    intro j
    rw [lengths_data]
    have h := (originalLengths_canonical input hC j).2.trans (rationalWordWidth_of_height (hLengths j))
    dsimp only [W]; omega
  have hScaleState : scale.1.1 = BinaryRationalOpcode.apply .mul (parameters.read 6) (parameters.read 5) :=
    BinarySmallUniformSplitMeasured.apply_state .mul _ _ (hP 6).1 (hP 5).1
  have hsWidth : width scale.1.1 ≤ W := by
    rw [hScaleState]
    have hc := BinaryReflectedFourSetup.opcode_canonical .mul _ _ (hP 6) (hP 5)
    have hh : RationalHeight (value (BinaryRationalOpcode.apply .mul (parameters.read 6) (parameters.read 5))) (t+t) := by
      rw [BinaryRationalOpcode.apply_value _ _ _ (hP 6).1 (hP 5).1]
      exact (hParameters 6).mul (hParameters 5)
    have h := hc.2.trans (rationalWordWidth_of_height hh)
    dsimp only [W]; omega
  have hLong : long.2 ≤ 1036 ∧ usage long.1.2 ≤ 617 :=
    ⟨BinaryThreeReferenceMeasured.references_work _ _,BinaryThreeReferenceMeasured.references_usage _ _⟩
  have hScale := opcode_bounds .mul (parameters.read 6) (parameters.read 5) W (hpWidth 6) (hpWidth 5)
  have hShort := fun j => opcode_bounds .mul (parameters.read 4) (long.1.1.read j) W (hpWidth 4) (hlWidth j)
  have hInitial := fun j => opcode_bounds .mul scale.1.1 (long.1.1.read j) W hsWidth (hlWidth j)
  have hShortW := BinaryLifetimeArrayMeasured.build_work_bound 3
    (fun j => BinaryQuadraticMeasured.apply .mul (parameters.read 4) (long.1.1.read j)) (opcodePrice W) (fun j => (hShort j).1)
  have hInitialW := BinaryLifetimeArrayMeasured.build_work_bound 3
    (fun j => BinaryQuadraticMeasured.apply .mul scale.1.1 (long.1.1.read j)) (opcodePrice W) (fun j => (hInitial j).1)
  have hShortU := BinaryLifetimeArrayMeasured.build_bounds 3
    (fun j => BinaryQuadraticMeasured.apply .mul (parameters.read 4) (long.1.1.read j)) (opcodeEnvelope W) (opcodeEnvelope W)
    (by intro j; have h := (hShort j).2; unfold usage at h; omega)
    (by intro j; have h := (hShort j).2; unfold usage at h; omega)
  have hInitialU := BinaryLifetimeArrayMeasured.build_bounds 3
    (fun j => BinaryQuadraticMeasured.apply .mul scale.1.1 (long.1.1.read j)) (opcodeEnvelope W) (opcodeEnvelope W)
    (by intro j; have h := (hInitial j).2; unfold usage at h; omega)
    (by intro j; have h := (hInitial j).2; unfold usage at h; omega)
  have hShortBounds : short.2 ≤ 3*opcodePrice W+1024 ∧ usage short.1.2 ≤ 4*opcodeEnvelope W+592 :=
    ⟨hShortW,hShortU.trans_eq (by unfold BinaryLifetimeArrayMeasured.storageReserve; omega)⟩
  have hInitialBounds : initial.2 ≤ 3*opcodePrice W+1024 ∧ usage initial.1.2 ≤ 4*opcodeEnvelope W+592 :=
    ⟨hInitialW,hInitialU.trans_eq (by unfold BinaryLifetimeArrayMeasured.storageReserve; omega)⟩
  have hResult := assemble_bounds (parameters.read 7) long scale short initial _ _ hLong hScale hShortBounds hInitialBounds
  rw [fromParameters_eq]
  simpa only [long,scale,short,initial,W,workEnvelope,envelope] using hResult

set_option cleanup.letToHave false in
def capacityWithExtras (system : System) : ((FixedArrayTable 3 SignedWord × Trace) × ℕ) × ℕ :=
  BinaryLifetimeArrayExtras.build 3 (fun j => BinaryNormalizedCoordinate.opcode .sub (system.long.read j) (system.short.read j))

def capacity (system : System) : (FixedArrayTable 3 SignedWord × Trace) × ℕ :=
  (capacityWithExtras system).1

theorem capacityWithExtras_compat (system : System) :
    (capacityWithExtras system).1 = capacity system := rfl

theorem capacity_record (system : System) :
    capacity system =
  BinaryLifetimeArrayMeasured.build 3 (fun j => BinaryPlannedQuadratic.apply .sub (system.long.read j) (system.short.read j)) := by
  simp only [capacity,capacityWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record,fromParametersWithExtras_compat]

theorem capacity_data (system : System) :
    (capacity system).1.1 = (BinaryReflectedSystemLifetime.capacityWithTrace system).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,capacity_record,BinaryReflectedSystemLifetime.capacityWithTrace,BinaryLifetimeArrayMeasured.build_data,
    BinaryQuadraticMeasured.apply_erases]

def capacityPrice (t : ℕ) : ℕ := 3*opcodePrice (2*t+1)+1024
def capacityEnvelope (t : ℕ) : ℕ := 4*opcodeEnvelope (2*t+1)+592

theorem capacity_bounds (system : System) (hC : system.Canonical) (t : ℕ)
    (hLong : ∀ j,RationalHeight (value (system.long.read j)) t)
    (hShort : ∀ j,RationalHeight (value (system.short.read j)) t) :
    (capacity system).2 ≤ capacityPrice t ∧ usage (capacity system).1.2 ≤ capacityEnvelope t := by
  have hEach := fun j => BinarySmallUniformPreparationMeasured.opcode_bounds .sub (system.long.read j) (system.short.read j)
    (hC.2.1 j) (hC.2.2.1 j) t (hLong j) (hShort j)
  have hW := BinaryLifetimeArrayMeasured.build_work_bound 3
    (fun j => BinaryQuadraticMeasured.apply .sub (system.long.read j) (system.short.read j))
    (BinarySmallUniformSplitMeasured.opcodePrice t) (fun j => (hEach j).1)
  have hU := BinaryLifetimeArrayMeasured.build_bounds 3
    (fun j => BinaryQuadraticMeasured.apply .sub (system.long.read j) (system.short.read j))
    (opcodeEnvelope (2*t+1)) (opcodeEnvelope (2*t+1))
    (by intro j; have h := (hEach j).2; unfold usage at h; omega)
    (by intro j; have h := (hEach j).2; unfold usage at h; omega)
  simp only [capacity_record, BinaryPlannedQuadratic.apply_previous]
  refine ⟨hW,?_⟩
  exact hU.trans_eq (by unfold capacityEnvelope BinaryLifetimeArrayMeasured.storageReserve; omega)

end Blotto.BinaryReflectedSystemMeasured
