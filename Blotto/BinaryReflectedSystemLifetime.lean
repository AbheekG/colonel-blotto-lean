import Blotto.BinaryReflectedParameterLifetime
import Blotto.BinaryReflectedSetupWork

/-! Actual reflected system production caches one scale and consumes traced
quadratic products/subtractions and array production. All versions stay live. -/
namespace Blotto.BinaryReflectedSystemLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryReflectedFourSetup BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 1500000

def fromParametersWithTrace (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) : System × Trace :=
  let lengths := originalLengths input
  let scale := BinaryQuadraticLifetime.applyWithTrace .mul (parameters.read 6) (parameters.read 5)
  let shorts := BinaryLifetimeArray.build 3
    (fun j => BinaryQuadraticLifetime.applyWithTrace .mul (parameters.read 4) (lengths.read j))
  let initial := BinaryLifetimeArray.build 3
    (fun j => BinaryQuadraticLifetime.applyWithTrace .mul scale.1 (lengths.read j))
  (⟨parameters.read 7,lengths,shorts.1,initial.1⟩,wrap 192 8 [scale.2,shorts.2,initial.2])

theorem fromParametersWithTrace_erasure (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord)
    (hC : input.Canonical) (hP : ∀ j,CanonicalWord (parameters.read j)) :
    (fromParametersWithTrace input parameters).1 = fromParameters input parameters := by
  have hScale := BinaryQuadraticLifetime.applyWithTrace_state .mul (parameters.read 6) (parameters.read 5) (hP 6).1 (hP 5).1
  have hScaleValid := BinaryRationalOpcode.apply_valid .mul _ _ (hP 6).1 (hP 5).1
  have hShort : (BinaryLifetimeArray.build 3
      (fun j => BinaryQuadraticLifetime.applyWithTrace .mul (parameters.read 4) ((originalLengths input).read j))).1 =
      FixedArrayTable.ofFn (fun j => BinaryRationalOpcode.apply .mul (parameters.read 4) ((originalLengths input).read j)) := by
    apply BinaryOverlapInputPreparation.table_ext
    intro j
    simp only [BinaryLifetimeArray.build_erases,FixedArrayTable.read_ofFn]
    exact BinaryQuadraticLifetime.applyWithTrace_state .mul _ _ (hP 4).1 (originalLengths_canonical input hC j).1
  have hInitial : (BinaryLifetimeArray.build 3
      (fun j => BinaryQuadraticLifetime.applyWithTrace .mul
        (BinaryQuadraticLifetime.applyWithTrace .mul (parameters.read 6) (parameters.read 5)).1
        ((originalLengths input).read j))).1 =
      FixedArrayTable.ofFn (fun j => BinaryRationalOpcode.apply .mul
        (BinaryRationalOpcode.apply .mul (parameters.read 6) (parameters.read 5)) ((originalLengths input).read j)) := by
    apply BinaryOverlapInputPreparation.table_ext
    intro j
    simp only [BinaryLifetimeArray.build_erases,FixedArrayTable.read_ofFn,hScale]
    exact BinaryQuadraticLifetime.applyWithTrace_state .mul _ _ hScaleValid (originalLengths_canonical input hC j).1
  unfold fromParametersWithTrace fromParameters
  dsimp only
  rw [hShort,hInitial]

def envelope (t : ℕ) : ℕ := 7 * opcodeEnvelope (4 * t + 1) + 512

theorem fromParametersWithTrace_usage (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord)
    (hC : input.Canonical) (hP : ∀ j,CanonicalWord (parameters.read j)) (t : ℕ)
    (hParameters : ∀ j,RationalHeight (value (parameters.read j)) t)
    (hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) t) :
    usage (fromParametersWithTrace input parameters).2 ≤ envelope t := by
  let W := 4 * t + 1
  have hpWidth : ∀ j,width (parameters.read j) ≤ W := by
    intro j
    have h := (hP j).2.trans (rationalWordWidth_of_height (hParameters j))
    dsimp only [W]
    omega
  have hlWidth : ∀ j,width ((originalLengths input).read j) ≤ W := by
    intro j
    have h := (originalLengths_canonical input hC j).2.trans (rationalWordWidth_of_height (hLengths j))
    dsimp only [W]
    omega
  let scale := BinaryQuadraticLifetime.applyWithTrace .mul (parameters.read 6) (parameters.read 5)
  have hsWidth : width scale.1 ≤ W := by
    dsimp only [scale]
    rw [BinaryQuadraticLifetime.applyWithTrace_state _ _ _ (hP 6).1 (hP 5).1]
    have hc := opcode_canonical .mul _ _ (hP 6) (hP 5)
    have hh : RationalHeight (value (BinaryRationalOpcode.apply .mul (parameters.read 6) (parameters.read 5))) (t + t) := by
      rw [BinaryRationalOpcode.apply_value _ _ _ (hP 6).1 (hP 5).1]
      exact (hParameters 6).mul (hParameters 5)
    have h := hc.2.trans (rationalWordWidth_of_height hh)
    dsimp only [W]
    omega
  have hScale := opcode_usage .mul (parameters.read 6) (parameters.read 5) W (hpWidth 6) (hpWidth 5)
  have hShort := fun j => BinaryQuadraticLifetime.applyWithTrace_bounds .mul (parameters.read 4)
    ((originalLengths input).read j) W (hpWidth 4) (hlWidth j)
  have hInitial := fun j => BinaryQuadraticLifetime.applyWithTrace_bounds .mul scale.1
    ((originalLengths input).read j) W hsWidth (hlWidth j)
  have hShortArray := array_usage 3 (fun j => BinaryQuadraticLifetime.applyWithTrace .mul (parameters.read 4)
    ((originalLengths input).read j)) (BinaryQuadraticLifetime.opcodeBound W) (BinaryQuadraticLifetime.opcodeFrames W)
    (fun j => (hShort j).1) (fun j => (hShort j).2)
  have hInitialArray := array_usage 3 (fun j => BinaryQuadraticLifetime.applyWithTrace .mul scale.1
    ((originalLengths input).read j)) (BinaryQuadraticLifetime.opcodeBound W) (BinaryQuadraticLifetime.opcodeFrames W)
    (fun j => (hInitial j).1) (fun j => (hInitial j).2)
  have hw := wrap_usage 192 8 [scale.2,
    (BinaryLifetimeArray.build 3 (fun j => BinaryQuadraticLifetime.applyWithTrace .mul (parameters.read 4)
      ((originalLengths input).read j))).2,
    (BinaryLifetimeArray.build 3 (fun j => BinaryQuadraticLifetime.applyWithTrace .mul scale.1
      ((originalLengths input).read j))).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 192 8 [scale.2,
    (BinaryLifetimeArray.build 3 (fun j => BinaryQuadraticLifetime.applyWithTrace .mul (parameters.read 4)
      ((originalLengths input).read j))).2,
    (BinaryLifetimeArray.build 3 (fun j => BinaryQuadraticLifetime.applyWithTrace .mul scale.1
      ((originalLengths input).read j))).2]) ≤ _
  change usage scale.2 ≤ opcodeEnvelope W at hScale
  unfold envelope
  dsimp only [W] at hScale hShortArray hInitialArray
  unfold opcodeEnvelope at *
  omega

def capacityWithTrace (system : System) : FixedArrayTable 3 SignedWord × Trace :=
  BinaryLifetimeArray.build 3
    (fun j => BinaryQuadraticLifetime.applyWithTrace .sub (system.long.read j) (system.short.read j))

theorem capacityWithTrace_erasure (system : System) (hC : system.Canonical) :
    (capacityWithTrace system).1 = system.capacity := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [capacityWithTrace,BinaryLifetimeArray.build_erases,System.capacity,FixedArrayTable.read_ofFn]
  exact BinaryQuadraticLifetime.applyWithTrace_state .sub _ _ (hC.2.1 j).1 (hC.2.2.1 j).1

def capacityEnvelope (t : ℕ) : ℕ := 3 * opcodeEnvelope (2 * t + 1) + 64

theorem capacityWithTrace_usage (system : System) (hC : system.Canonical) (t : ℕ)
    (hLong : ∀ j,RationalHeight (value (system.long.read j)) t)
    (hShort : ∀ j,RationalHeight (value (system.short.read j)) t) :
    usage (capacityWithTrace system).2 ≤ capacityEnvelope t := by
  have hEach := fun j => BinaryQuadraticLifetime.applyWithTrace_bounds .sub (system.long.read j) (system.short.read j)
    (2 * t + 1) (by have h := (hC.2.1 j).2.trans (rationalWordWidth_of_height (hLong j)); omega)
    (by have h := (hC.2.2.1 j).2.trans (rationalWordWidth_of_height (hShort j)); omega)
  have h := array_usage 3 (fun j => BinaryQuadraticLifetime.applyWithTrace .sub (system.long.read j) (system.short.read j))
    (BinaryQuadraticLifetime.opcodeBound (2 * t + 1)) (BinaryQuadraticLifetime.opcodeFrames (2 * t + 1))
    (fun j => (hEach j).1) (fun j => (hEach j).2)
  unfold capacityWithTrace capacityEnvelope opcodeEnvelope
  omega

end Blotto.BinaryReflectedSystemLifetime
