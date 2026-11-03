import Blotto.BinarySmallUniformFactoryMeasured
import Blotto.BinaryWordSegmentMeasured
import Blotto.BinaryFourSmallUniformDrawLifetime

/-! The returned measured nine-slot small-uniform descriptor feeds the complete measured
categorical/physical-point draw once. Exact old row/cursor behavior and original
six-field-derived source work and retained-prefix bounds are preserved. Native
label/reference/observer/allocator prices remain separate. -/

namespace Blotto.BinaryFourSmallUniformDrawMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3500000

set_option cleanup.letToHave false in
def preparedWithExtras (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) : ((BinaryStoredSegmentProgram.Prepared 4 9 × Trace) × ℕ) × ℕ :=
  let produced := BinarySmallUniformFactoryMeasured.descriptorWithExtras input
  let descriptor := produced.1
  have hData : descriptor.1.1 = BinarySmallUniformCompiler.fromOriginal input := by
    simpa only [descriptor,produced,BinarySmallUniformFactoryMeasured.descriptorWithExtras_compat] using
      (BinarySmallUniformFactoryMeasured.descriptor_data input).trans (BinarySmallUniformFactoryLifetime.fromOriginalWithTrace_erasure input hC)
  (((⟨descriptor.1.1,
    by rw [hData]; exact BinarySmallUniformCompiler.fromOriginal_canonical input hC,
    by rw [hData]; exact BinarySmallRootSample.uniform_nonnegative input hC hAd⟩,descriptor.1.2),descriptor.2+4),produced.2)

def prepared (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) :
    (BinaryStoredSegmentProgram.Prepared 4 9 × Trace) × ℕ :=
  (preparedWithExtras input hC hAd).1

theorem preparedWithExtras_compat (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) :
    (preparedWithExtras input hC hAd).1 = prepared input hC hAd := rfl

theorem prepared_record (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) :
    prepared input hC hAd =
  let descriptor := BinarySmallUniformFactoryMeasured.descriptor input
  have hData : descriptor.1.1 = BinarySmallUniformCompiler.fromOriginal input :=
    (BinarySmallUniformFactoryMeasured.descriptor_data input).trans
      (BinarySmallUniformFactoryLifetime.fromOriginalWithTrace_erasure input hC)
  ((⟨descriptor.1.1,
    by rw [hData]; exact BinarySmallUniformCompiler.fromOriginal_canonical input hC,
    by rw [hData]; exact BinarySmallRootSample.uniform_nonnegative input hC hAd⟩,descriptor.1.2),descriptor.2+4) := by
  simp only [prepared,preparedWithExtras,BinarySmallUniformFactoryMeasured.descriptorWithExtras_compat]

theorem prepared_data (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) :
    (prepared input hC hAd).1.1 = (BinaryFourSmallUniformDrawLifetime.preparedWithTrace input hC hAd).1 := by
  simp only [prepared_record]
  unfold BinaryFourSmallUniformDrawLifetime.preparedWithTrace
  simp only [BinarySmallUniformFactoryMeasured.descriptor_data]

set_option cleanup.letToHave false in
def runWithFactoryExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((BinaryPRGWordControllerSegment.Result store 4 × Trace) × ℕ) × ℕ) × ℕ :=
  let prepared := preparedWithExtras input hC hAd
  let held := prepared.1
  let produced := BinaryWordSegmentMeasured.runWithExtras store held.1.1 0 K scalar pc hp
  let drawn := produced.1
  ((((drawn.1.1,wrap 32 2 [held.1.2,drawn.1.2]),held.2+drawn.2+8),produced.2),prepared.2)

def runWithDrawExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerSegment.Result store 4 × Trace) × ℕ) × ℕ :=
  (runWithFactoryExtras store input hC hAd K scalar pc hp).1

theorem runWithFactoryExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K scalar pc hp).1 = runWithDrawExtras store input hC hAd K scalar pc hp := rfl

theorem runWithDrawExtras_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    runWithDrawExtras store input hC hAd K scalar pc hp =
  let held := prepared input hC hAd
  let produced := BinaryWordSegmentMeasured.runWithExtras store held.1.1 0 K scalar pc hp
  let drawn := produced.1
  (((drawn.1.1,wrap 32 2 [held.1.2,drawn.1.2]),held.2+drawn.2+8),produced.2) := by
  simp only [runWithDrawExtras,runWithFactoryExtras,BinarySmallUniformFactoryMeasured.descriptorWithExtras_compat,preparedWithExtras_compat]

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerSegment.Result store 4 × Trace) × ℕ :=
  (runWithDrawExtras store input hC hAd K scalar pc hp).1

theorem runWithDrawExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithDrawExtras store input hC hAd K scalar pc hp).1 = run store input hC hAd K scalar pc hp := rfl

theorem run_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    run store input hC hAd K scalar pc hp =
  let held := prepared input hC hAd
  let drawn := BinaryWordSegmentMeasured.run store held.1.1 0 K scalar pc hp
  ((drawn.1.1,wrap 32 2 [held.1.2,drawn.1.2]),held.2+drawn.2+8) := by
  simp only [run,runWithDrawExtras_record,BinaryWordSegmentMeasured.runWithExtras_compat]

theorem run_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K scalar pc hp).1.1 =
      (BinaryFourSmallUniformDrawLifetime.runWithTrace store input hC hAd K scalar pc hp).1 := by
  simp only [run_record,BinaryFourSmallUniformDrawLifetime.runWithTrace,prepared_data,BinaryWordSegmentMeasured.run_erases]

def workEnvelope (s K i cap : ℕ) : ℕ := BinarySmallUniformFactoryMeasured.workEnvelope s+
  BinaryWordSegmentMeasured.workEnvelope 4 9 (expressionHeightBudget s 35) K i cap+12
def envelope (s K i cap : ℕ) : ℕ := BinarySmallUniformFactoryMeasured.envelope s+
  BinaryWordSegmentLifetimeBound.envelope 4 9 (expressionHeightBudget s 35) K i cap+64

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K scalar pc hp).2 ≤ workEnvelope s K store.width store.cap.value ∧
      usage (run store input hC hAd K scalar pc hp).1.2 ≤ envelope s K store.width store.cap.value := by
  let held := prepared input hC hAd
  let drawn := BinaryWordSegmentMeasured.run store held.1.1 0 K scalar pc hp
  have hErasure := (prepared_data input hC hAd).trans (BinaryFourSmallUniformDrawLifetime.preparedWithTrace_erasure input hC hAd)
  have hRef : held.1.1.table.Refines (source.smallUniformLottery hCase) := by
    dsimp only [held]
    rw [hErasure]
    exact BinarySmallUniformCompiler.fromOriginal_refines input source hC hR hCase
  have hHeight := hH.smallUniformLottery (by omega : 2 ≤ s) hCase
  have hs35 : 3 ≤ expressionHeightBudget s 35 := hs.trans (expressionHeightBudget_ge_input s 35)
  have hFactory := BinarySmallUniformFactoryMeasured.descriptor_bounds input source hC hR hCase s hs hH
  have hDrawW := BinaryWordSegmentMeasured.run_work store held.1.1 (source.smallUniformLottery hCase) hRef
    (expressionHeightBudget s 35) hHeight.1 hHeight.2 0 K scalar pc hp
  have hDrawU := BinaryWordSegmentMeasured.run_usage store held.1.1 (source.smallUniformLottery hCase) hRef
    (expressionHeightBudget s 35) hs35 hHeight.1 hHeight.2 0 K scalar pc hp
  have hFactoryW : held.2 ≤ BinarySmallUniformFactoryMeasured.workEnvelope s+4 := by
    change (BinarySmallUniformFactoryMeasured.descriptor input).2+4 ≤ _
    omega
  have hFactoryU : usage held.1.2 ≤ BinarySmallUniformFactoryMeasured.envelope s := hFactory.2
  change drawn.2 ≤ _ at hDrawW
  change usage drawn.1.2 ≤ _ at hDrawU
  have hw := wrap_usage 32 2 [held.1.2,drawn.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change held.2+drawn.2+8 ≤ _ ∧ usage (wrap 32 2 [held.1.2,drawn.1.2]) ≤ _
  unfold workEnvelope envelope
  exact ⟨by omega,by omega⟩

theorem run_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K scalar pc hp).1.1.2.value ∧
      (run store input hC hAd K scalar pc hp).1.1.2.value ≤ store.cap.value :=
  BinaryWordSegmentMeasured.run_position store (prepared input hC hAd).1.1 0 K scalar pc hp

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC hAd K scalar pc hp).1.2 steps ≤ borrowed+envelope s K store.width store.cap.value ∧
      framePeak ((run store input hC hAd K scalar pc hp).1.2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp).2 borrowed steps

end Blotto.BinaryFourSmallUniformDrawMeasured
