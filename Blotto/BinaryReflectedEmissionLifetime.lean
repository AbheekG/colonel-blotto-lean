import Blotto.BinaryScalarTape
import Blotto.BinaryReflectedTerminalFactoryLifetime
import Blotto.BinaryWordSegmentLifetimeBound

/-! Selected reflected emission uses the actual retained table: one traced
midpoint/interpolation, three traced original-length subtractions and a retained
four-word output with final zero. -/
namespace Blotto.BinaryReflectedEmissionLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage BinaryReflectedFourSetup
set_option maxHeartbeats 2000000

abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def reflectWithTrace (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) :
    FixedArrayTable 4 SignedWord × Trace :=
  let differences := BinaryLifetimeArray.build 3 (fun j =>
    BinaryQuadraticLifetime.applyWithTrace .sub ((originalLengths input).read j) (row.read j))
  let output := BinaryNestedResidualLifetime.copyWithTrace 4
    ![differences.1.read 0,differences.1.read 1,differences.1.read 2,BinaryRationalOpcode.zero]
  (output.1,wrap 32 2 [differences.2,output.2])

theorem reflectWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (row : FixedArrayTable 3 SignedWord) (hRow : ∀ j,CanonicalWord (row.read j)) :
    (reflectWithTrace input row).1 = reflect input row := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  fin_cases j
  · change (BinaryQuadraticLifetime.applyWithTrace .sub input.u (row.read 0)).1 =
      BinaryRationalOpcode.apply .sub input.u (row.read 0)
    exact BinaryQuadraticLifetime.applyWithTrace_state .sub _ _ hC.2.1.1 (hRow 0).1
  · change (BinaryQuadraticLifetime.applyWithTrace .sub input.v (row.read 1)).1 =
      BinaryRationalOpcode.apply .sub input.v (row.read 1)
    exact BinaryQuadraticLifetime.applyWithTrace_state .sub _ _ hC.2.2.1.1 (hRow 1).1
  · change (BinaryQuadraticLifetime.applyWithTrace .sub input.w (row.read 2)).1 =
      BinaryRationalOpcode.apply .sub input.w (row.read 2)
    exact BinaryQuadraticLifetime.applyWithTrace_state .sub _ _ hC.2.2.2.1.1 (hRow 2).1
  · rfl

def reflectEnvelope (W : ℕ) : ℕ := 4 * opcodeEnvelope W + 512

theorem reflectWithTrace_usage (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord)
    (W : ℕ) (hLengths : ∀ j,width ((originalLengths input).read j) ≤ W)
    (hRow : ∀ j,width (row.read j) ≤ W) :
    usage (reflectWithTrace input row).2 ≤ reflectEnvelope W := by
  let differences := BinaryLifetimeArray.build 3 (fun j =>
    BinaryQuadraticLifetime.applyWithTrace .sub ((originalLengths input).read j) (row.read j))
  let output := BinaryNestedResidualLifetime.copyWithTrace 4
    ![differences.1.read 0,differences.1.read 1,differences.1.read 2,BinaryRationalOpcode.zero]
  have hEach := fun j => opcode_usage .sub ((originalLengths input).read j) (row.read j)
    W (hLengths j) (hRow j)
  have hDifferences := array_usage 3 (fun j =>
    BinaryQuadraticLifetime.applyWithTrace .sub ((originalLengths input).read j) (row.read j))
    (opcodeEnvelope W) (opcodeEnvelope W)
    (by intro j; have h := hEach j; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at h; omega)
    (by intro j; have h := hEach j; unfold usage at h; omega)
  change usage differences.2 ≤ _ at hDifferences
  have hOutput := BinaryNestedResidualLifetime.copyWithTrace_usage 4
    ![differences.1.read 0,differences.1.read 1,differences.1.read 2,BinaryRationalOpcode.zero]
  change usage output.2 ≤ _ at hOutput
  have hw := wrap_usage 32 2 [differences.2,output.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [differences.2,output.2]) ≤ _
  unfold reflectEnvelope BinaryNestedResidualLifetime.copyEnvelope at *
  omega

def sampleWithTrace (input : BinaryFourParameters.Input) (table : Segment) (slot : Fin 18)
    (K : ℕ) (scalar : BinaryScalarTape K) : FixedArrayTable 4 SignedWord × Trace :=
  let point := BinaryQuadraticPointLifetime.sampleWithTrace table slot K scalar
  let output := reflectWithTrace input point.1
  (output.1,wrap 32 2 [point.2,output.2])

theorem sampleWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (table : Segment) (hTable : table.Canonical) (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) :
    (sampleWithTrace input table slot K scalar).1 = reflect input (BinarySegmentPoint.sample table slot K scalar) := by
  have hPoint := BinaryQuadraticPointLifetime.sampleWithTrace_state table hTable slot K scalar
  have hPointC : ∀ j,CanonicalWord
      ((BinaryQuadraticPointLifetime.sampleWithTrace table slot K scalar).1.read j) := by
    rw [hPoint]
    exact BinarySegmentPoint.sample_canonical table slot K scalar hTable
  unfold sampleWithTrace
  dsimp only
  rw [reflectWithTrace_erasure input hC _ hPointC,hPoint]

def envelope (s K : ℕ) : ℕ :=
  BinaryQuadraticPointLifetime.bound 3 s K + BinaryQuadraticPointLifetime.frames 3 s K +
    reflectEnvelope (2 * expressionHeightBudget (max s (K+2)) 3 + 1) + 128

theorem sampleWithTrace_usage (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (table : Segment) (hTable : table.Canonical) (source : RationalSegmentLottery 3 18)
    (hR : table.Refines source) (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s)
    (hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) s)
    (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) :
    usage (sampleWithTrace input table slot K scalar).2 ≤ envelope s K := by
  let point := BinaryQuadraticPointLifetime.sampleWithTrace table slot K scalar
  let H := expressionHeightBudget (max s (K+2)) 3
  have hEndpoints : ∀ i j,RationalHeight (value ((table.P.read i).read j)) s ∧
      RationalHeight (value ((table.Q.read i).read j)) s := by
    intro i j
    rw [hR.2.1 i j,hR.2.2 i j]
    exact hHeight.2 i j
  have hPoint := BinaryQuadraticPointLifetime.sampleWithTrace_bounds table hTable s hs hEndpoints slot K scalar
  have hPointUsage : usage point.2 ≤
      BinaryQuadraticPointLifetime.bound 3 s K + BinaryQuadraticPointLifetime.frames 3 s K := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    exact Nat.add_le_add hPoint.1 hPoint.2
  have hPointState := BinaryQuadraticPointLifetime.sampleWithTrace_state table hTable slot K scalar
  have hPointC : ∀ j,CanonicalWord (point.1.read j) := by
    rw [hPointState]
    exact BinarySegmentPoint.sample_canonical table slot K scalar hTable
  have hPointH : ∀ j,RationalHeight (value (point.1.read j)) H := by
    intro j
    rw [hPointState,BinarySegmentPoint.sample_value table source hTable hR slot K scalar j]
    exact hHeight.point (by omega) K slot scalar j
  have hRowWidth : ∀ j,width (point.1.read j) ≤ 2*H+1 := by
    intro j
    have h := (hPointC j).2.trans (rationalWordWidth_of_height (hPointH j))
    omega
  have hLengthsWidth : ∀ j,width ((originalLengths input).read j) ≤ 2*H+1 := by
    intro j
    have h := (originalLengths_canonical input hC j).2.trans (rationalWordWidth_of_height (hLengths j))
    have hm := (le_max_left s (K+2)).trans (expressionHeightBudget_ge_input _ 3)
    dsimp only [H] at hm ⊢
    omega
  have hReflect := reflectWithTrace_usage input point.1 (2*H+1) hLengthsWidth hRowWidth
  have hw := wrap_usage 32 2 [point.2,(reflectWithTrace input point.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [point.2,(reflectWithTrace input point.1).2]) ≤ _
  unfold envelope
  dsimp only [H] at hReflect ⊢
  omega

theorem all_prefix (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (table : Segment) (hTable : table.Canonical) (source : RationalSegmentLottery 3 18)
    (hR : table.Refines source) (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s)
    (hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) s)
    (slot : Fin 18) (K : ℕ) (scalar : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (sampleWithTrace input table slot K scalar).2 steps ≤ borrowed + envelope s K ∧
    framePeak ((sampleWithTrace input table slot K scalar).2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (sampleWithTrace_usage input hC table hTable source hR s hs hHeight hLengths slot K scalar) borrowed steps

end Blotto.BinaryReflectedEmissionLifetime
