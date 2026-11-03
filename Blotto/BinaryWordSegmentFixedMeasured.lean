import Blotto.BinaryWordSegmentMeasured
import Blotto.BinaryCategoricalLowerMeasured
import Blotto.BinaryWordSegmentFixedLifetime

/-! One retained table feeds actual measured optional selection/point work and,
only on exhaustion, measured deterministic lower selection/point work. The
fallback consumes no coin input and preserves the returned absolute cursor. -/
namespace Blotto.BinaryWordSegmentFixedMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryStoredSegmentProgram
set_option autoImplicit false
set_option maxHeartbeats 1200000

set_option cleanup.letToHave false in
def lowerWithExtras {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) : ((FixedArrayTable n SignedWord × Trace) × ℕ) × ℕ :=
  let produced := BinaryCategoricalLowerMeasured.segmentWithExtras prepared fallback
  let selected := produced.1
  let result := BinaryPhysicalPointMeasured.sampleWithExtras prepared.table selected.1.1 K scalar
  let point := result.1
  (((point.1.1,wrap 24 2 [selected.1.2,point.1.2]),selected.2+point.2+8),produced.2+result.2)

def lower {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) :
    (FixedArrayTable n SignedWord × Trace) × ℕ :=
  (lowerWithExtras prepared fallback K scalar).1

theorem lowerWithExtras_compat {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) : (lowerWithExtras prepared fallback K scalar).1 = lower prepared fallback K scalar := rfl

theorem lower_record {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) : lower prepared fallback K scalar =
  let selected := BinaryCategoricalLowerMeasured.segment prepared fallback
  let point := BinaryPhysicalPointMeasured.sample prepared.table selected.1.1 K scalar
  ((point.1.1,wrap 24 2 [selected.1.2,point.1.2]),selected.2+point.2+8) := by
  rfl

theorem lower_erases {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) :
    (lower prepared fallback K scalar).1 = BinaryWordSegmentFixedLifetime.lowerWithTrace prepared fallback K scalar := by
  simp only [lower_record,BinaryWordSegmentFixedLifetime.lowerWithTrace,BinaryCategoricalLowerMeasured.segment_erases,
    BinaryPhysicalPointMeasured.sample_erases,BinaryQuadraticPointLifetime.sampleWithTrace]

def lowerPrice (n k s K : ℕ) : ℕ := BinaryCategoricalLowerMeasured.workEnvelope k s+BinaryPhysicalPointMeasured.price n s K+8

theorem lower_work {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (source : RationalSegmentLottery n k)
    (hR : prepared.table.Refines source) (s : ℕ) (hHeight : source.HeightAt s) (K : ℕ) (scalar : BinaryScalarTape K) :
    (lower prepared fallback K scalar).2 ≤ lowerPrice n k s K := by
  let selected := BinaryCategoricalLowerMeasured.segment prepared fallback
  have hSelected := BinaryCategoricalLowerMeasured.segment_work prepared source hR s hHeight.1 fallback
  have hEndpoint : ∀ slot j,RationalHeight (value ((prepared.table.P.read slot).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) s := by
    intro slot j; rw [hR.2.1 slot j,hR.2.2 slot j]; exact hHeight.2 slot j
  have hPoint := BinaryPhysicalPointMeasured.sample_work prepared.table prepared.canonical s hEndpoint selected.1.1 K scalar
  change selected.2+(BinaryPhysicalPointMeasured.sample prepared.table selected.1.1 K scalar).2+8 ≤ _
  unfold lowerPrice
  change selected.2 ≤ _ at hSelected
  omega

set_option cleanup.letToHave false in
def runWithExtras {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((FixedArrayTable n SignedWord × FixedBinaryWord store.width) × Trace) × ℕ) × ℕ :=
  let produced := BinaryWordSegmentMeasured.runWithExtras store prepared fallback K scalar pc hp
  let drawn := produced.1
  match drawn.1.1.1 with
  | some row => ((((row,drawn.1.1.2),wrap 24 2 [drawn.1.2]),drawn.2+4),produced.2)
  | none =>
      let result := lowerWithExtras prepared fallback K scalar
      let fallbackRow := result.1
      ((((fallbackRow.1.1,drawn.1.1.2),wrap 32 2 [drawn.1.2,fallbackRow.1.2]),drawn.2+fallbackRow.2+8),produced.2+result.2)

def run {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((FixedArrayTable n SignedWord × FixedBinaryWord store.width) × Trace) × ℕ :=
  (runWithExtras store prepared fallback K scalar pc hp).1

theorem runWithExtras_compat {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (runWithExtras store prepared fallback K scalar pc hp).1 = run store prepared fallback K scalar pc hp := rfl

theorem run_record {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : run store prepared fallback K scalar pc hp =
  let drawn := BinaryWordSegmentMeasured.run store prepared fallback K scalar pc hp
  match drawn.1.1.1 with
  | some row => (((row,drawn.1.1.2),wrap 24 2 [drawn.1.2]),drawn.2+4)
  | none =>
      let fallbackRow := lower prepared fallback K scalar
      (((fallbackRow.1.1,drawn.1.1.2),wrap 32 2 [drawn.1.2,fallbackRow.1.2]),drawn.2+fallbackRow.2+8) := by
  simp only [run,runWithExtras,BinaryWordSegmentMeasured.runWithExtras_compat]
  cases h : (BinaryWordSegmentMeasured.run store prepared fallback K scalar pc hp).1.1.1 with
  | none => simp only [h,lowerWithExtras_compat]
  | some row => simp only [h]

theorem run_erases {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared fallback K scalar pc hp).1 = BinaryWordSegmentFixedLifetime.runWithTrace store prepared fallback K scalar pc hp := by
  simp only [run_record,BinaryWordSegmentFixedLifetime.runWithTrace,BinaryWordSegmentMeasured.run_erases,lower_erases]
  cases (BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp).1.1 <;> rfl

def workEnvelope (n k s K i cap : ℕ) : ℕ := BinaryWordSegmentMeasured.workEnvelope n k s K i cap+lowerPrice n k s K+8

theorem run_work {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source) (s : ℕ) (hHeight : source.HeightAt s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared fallback K scalar pc hp).2 ≤ workEnvelope n k s K store.width store.cap.value := by
  let drawn := BinaryWordSegmentMeasured.run store prepared fallback K scalar pc hp
  have hDraw := BinaryWordSegmentMeasured.run_work store prepared source hR s hHeight.1 hHeight.2 fallback K scalar pc hp
  have hLower := lower_work prepared fallback source hR s hHeight K scalar
  change drawn.2 ≤ _ at hDraw
  rw [run_record]
  dsimp only
  cases h : drawn.1.1.1 with
  | some row => change drawn.2+4 ≤ _; unfold workEnvelope; omega
  | none => change drawn.2+(lower prepared fallback K scalar).2+8 ≤ _; unfold workEnvelope; omega

theorem run_bounds {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source) (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared fallback K scalar pc hp).2 ≤ workEnvelope n k s K store.width store.cap.value ∧
      usage (run store prepared fallback K scalar pc hp).1.2 ≤ BinaryWordSegmentFixedLifetime.envelope n k s K store.width store.cap.value := by
  refine ⟨run_work store prepared fallback source hR s hHeight K scalar pc hp,?_⟩
  rw [run_erases]
  exact BinaryWordSegmentFixedLifetime.runWithTrace_usage store prepared fallback source hR s hs hHeight K scalar pc hp

theorem run_window {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared fallback K scalar pc hp).1.1.1 = prepared.sample fallback K (store.cap.value-pc.value) scalar
      (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value (store.cap.value-pc.value) (by omega)) := by
  rw [run_erases]
  exact BinaryWordSegmentFixedLifetime.runWithTrace_window store prepared fallback K scalar pc hp

theorem run_position {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store prepared fallback K scalar pc hp).1.1.2.value ∧ (run store prepared fallback K scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_erases]
  exact BinaryWordSegmentFixedLifetime.runWithTrace_position store prepared fallback K scalar pc hp

theorem run_cursor {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared fallback K scalar pc hp).1.1.2 = (BinaryPRGWordControllerSegment.run store prepared fallback K scalar pc hp).2 := by
  rw [run_erases]
  exact BinaryWordSegmentFixedLifetime.runWithTrace_cursor store prepared fallback K scalar pc hp

theorem all_prefix {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source) (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store prepared fallback K scalar pc hp).1.2 steps ≤ borrowed+BinaryWordSegmentFixedLifetime.envelope n k s K store.width store.cap.value ∧
      framePeak ((run store prepared fallback K scalar pc hp).1.2.take steps) ≤ BinaryWordSegmentFixedLifetime.envelope n k s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store prepared fallback source hR s hs hHeight K scalar pc hp).2 borrowed steps

end Blotto.BinaryWordSegmentFixedMeasured
