import Blotto.BinaryWordCategoricalMeasured
import Blotto.BinaryPhysicalPointMeasured
import Blotto.BinaryWordSegmentLifetimeBound

/-! Actual categorical selection feeds the selected measured physical point.
The complete old optional row/cursor/trace is preserved, including exhaustion.
Original normalized weights and endpoint heights derive source work; source
weight-list/control reservations leave native labels/references/observers and
allocator realization as explicit model obligations. -/

namespace Blotto.BinaryWordSegmentMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization BinaryRationalEncoding
open BinaryStoredSegmentProgram BinaryStoredSegmentChoiceWork
set_option autoImplicit false
set_option maxHeartbeats 4000000

set_option cleanup.letToHave false in
def selectWithExtras {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((Option (Fin k) × FixedBinaryWord store.width) × Trace) × ℕ) × ℕ :=
  let weights := NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative
  let produced := BinaryWordCategoricalMeasured.runWithExtras store fallback weights pc hp
  let selected := produced.1
  (((selected.1.1,wrapList k (8*k+16) (k+4) [selected.1.2]),selected.2+16*(k+1)^2+8),produced.2)

def select {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((Option (Fin k) × FixedBinaryWord store.width) × Trace) × ℕ :=
  (selectWithExtras store prepared fallback pc hp).1

theorem selectWithExtras_compat {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (selectWithExtras store prepared fallback pc hp).1 = select store prepared fallback pc hp := rfl

theorem select_record {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : select store prepared fallback pc hp =
  let weights := NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative
  let selected := BinaryWordCategoricalMeasured.run store fallback weights pc hp
  ((selected.1.1,wrapList k (8*k+16) (k+4) [selected.1.2]),selected.2+16*(k+1)^2+8) := by
  rfl

theorem select_erases {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (select store prepared fallback pc hp).1 = BinaryWordSegmentLifetime.selectWithTrace store prepared fallback pc hp := by
  simp only [select_record,BinaryWordSegmentLifetime.selectWithTrace,BinaryWordCategoricalMeasured.run_erases]

set_option cleanup.letToHave false in
def runWithExtras {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerSegment.Result store n × Trace) × ℕ) × ℕ :=
  let produced := selectWithExtras store prepared fallback pc hp
  let selected := produced.1
  match selected.1.1.1 with
  | none => ((((none,selected.1.1.2),wrap 16 2 [selected.1.2]),selected.2+4),produced.2)
  | some slot =>
      let result := BinaryPhysicalPointMeasured.sampleWithExtras prepared.table slot K scalar
      let point := result.1
      ((((some point.1.1,selected.1.1.2),wrap 24 2 [selected.1.2,point.1.2]),selected.2+point.2+8),produced.2+result.2)

def run {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerSegment.Result store n × Trace) × ℕ :=
  (runWithExtras store prepared fallback K scalar pc hp).1

theorem runWithExtras_compat {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (runWithExtras store prepared fallback K scalar pc hp).1 = run store prepared fallback K scalar pc hp := rfl

theorem run_record {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : run store prepared fallback K scalar pc hp =
  let selected := select store prepared fallback pc hp
  match selected.1.1.1 with
  | none => (((none,selected.1.1.2),wrap 16 2 [selected.1.2]),selected.2+4)
  | some slot =>
      let point := BinaryPhysicalPointMeasured.sample prepared.table slot K scalar
      (((some point.1.1,selected.1.1.2),wrap 24 2 [selected.1.2,point.1.2]),selected.2+point.2+8) := by
  simp only [run,runWithExtras,selectWithExtras_compat]
  cases hs : (select store prepared fallback pc hp).1.1.1 with
  | none => simp only [hs]
  | some slot => simp only [hs,BinaryPhysicalPointMeasured.sampleWithExtras_compat]

theorem run_erases {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared fallback K scalar pc hp).1 =
      BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp := by
  simp only [run_record,BinaryWordSegmentLifetime.runWithTrace,select_erases]
  cases hs : (BinaryWordSegmentLifetime.selectWithTrace store prepared fallback pc hp).1.1 with
  | none => rfl
  | some slot => simp only [BinaryPhysicalPointMeasured.sample_erases,BinaryQuadraticPointLifetime.sampleWithTrace]

def sourceStepPrice (k s i cap : ℕ) : ℕ :=
  let b := 1+k*s
  (k+1)*(11000*(1+2*b+1)^2+8)+12000*(2*b+2)^2+32+
    (20*(5+8*b)+24+(cap+1)*(100*((5+8*b)+i+2)))+16

theorem step_source (D k s i cap : ℕ) (hWidth : binaryWordWidth D ≤ 1+k*s) :
    BinaryWordCategoricalMeasured.stepPrice D k i cap ≤ sourceStepPrice k s i cap := by
  unfold BinaryWordCategoricalMeasured.stepPrice BinaryQuadraticCategoricalMeasured.preparationPrice
    BinaryQuadraticCategoricalMeasured.sumStepPrice BinaryQuadraticCategoricalMeasured.operandWidth
    BinaryQuadraticExpression.uniformPrice BinaryWordCoinMeasured.samplePrice BinaryWordCoinMeasured.localPrice sourceStepPrice
  dsimp only
  gcongr

def selectionPrice (k s i cap : ℕ) : ℕ := (k+1)*sourceStepPrice k s i cap+16*(k+1)^2+8
def workEnvelope (n k s K i cap : ℕ) : ℕ := selectionPrice k s i cap+BinaryPhysicalPointMeasured.price n s K+8

theorem select_work {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hHeight : ∀ slot,RationalHeight (source.weight slot) s)
    (fallback : Fin k) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (select store prepared fallback pc hp).2 ≤ selectionPrice k s store.width store.cap.value := by
  have hWidth := denominator_width prepared.table s (fun slot => by rw [hR.1 slot]; exact hHeight slot)
  have hUnit := source_unit prepared source hR
  have hLength : (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative).items.length = k := List.length_ofFn
  have hCat := BinaryWordCategoricalMeasured.run_work (denominator prepared.table) (denominator_positive prepared.table) k store fallback
    (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) hUnit (by rw [hLength]) pc hp
  rw [hLength] at hCat
  have hStep := Nat.mul_le_mul_left (k+1) (step_source (denominator prepared.table) k s store.width store.cap.value hWidth)
  rw [select_record]
  change _+16*(k+1)^2+8 ≤ _
  unfold selectionPrice
  omega

theorem run_work {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hWeight : ∀ slot,RationalHeight (source.weight slot) s)
    (hEndpoint : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared fallback K scalar pc hp).2 ≤ workEnvelope n k s K store.width store.cap.value := by
  have hSelect := select_work store prepared source hR s hWeight fallback pc hp
  have hTable : ∀ slot j,RationalHeight (value ((prepared.table.P.read slot).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) s := by
    intro slot j
    rw [hR.2.1 slot j,hR.2.2 slot j]
    exact hEndpoint slot j
  rw [run_record]
  dsimp only
  cases hs : (select store prepared fallback pc hp).1.1.1 with
  | none => simp only; unfold workEnvelope; omega
  | some slot =>
      have hPoint := BinaryPhysicalPointMeasured.sample_work prepared.table prepared.canonical s hTable slot K scalar
      simp only
      unfold workEnvelope
      omega

theorem run_position {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store prepared fallback K scalar pc hp).1.1.2.value ∧
      (run store prepared fallback K scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_erases]
  exact BinaryWordSegmentLifetime.runWithTrace_position store prepared fallback K scalar pc hp

theorem run_usage {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hWeight : ∀ slot,RationalHeight (source.weight slot) s)
    (hEndpoint : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (run store prepared fallback K scalar pc hp).1.2 ≤ BinaryWordSegmentLifetimeBound.envelope n k s K store.width store.cap.value := by
  rw [run_erases]
  exact BinaryWordSegmentLifetimeBound.runWithTrace_usage store prepared source hR s hs hWeight hEndpoint fallback K scalar pc hp

theorem all_prefix {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hWeight : ∀ slot,RationalHeight (source.weight slot) s)
    (hEndpoint : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (run store prepared fallback K scalar pc hp).1.2 steps ≤
      borrowed+BinaryWordSegmentLifetimeBound.envelope n k s K store.width store.cap.value ∧
    framePeak ((run store prepared fallback K scalar pc hp).1.2.take steps) ≤
      BinaryWordSegmentLifetimeBound.envelope n k s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (run_usage store prepared source hR s hs hWeight hEndpoint fallback K scalar pc hp) borrowed steps

end Blotto.BinaryWordSegmentMeasured
