import Blotto.BinaryFourGluingMeasured
import Blotto.BinaryWordSegmentMeasured
import Blotto.BinaryFourGluingDrawLifetime

/-! The returned measured 81-slot gluing descriptor feeds the complete measured
categorical/physical-point draw once. Exact old row/cursor behavior and original
six-field-derived source work and retained-prefix bounds are preserved. Native
label/reference/observer/allocator prices remain separate. -/

namespace Blotto.BinaryFourGluingDrawMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3500000

set_option cleanup.letToHave false in
def preparedWithExtras (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) : ((BinaryStoredSegmentProgram.Prepared 4 81 × Trace) × ℕ) × ℕ :=
  let produced := BinaryFourGluingMeasured.descriptorWithExtras input hC
  let descriptor := produced.1
  have hData : descriptor.1.1 = BinaryFourParentCompiler.descriptor input := by
    simpa only [descriptor,produced,BinaryFourGluingMeasured.descriptorWithExtras_compat] using
      (BinaryFourGluingMeasured.descriptor_data input hC).trans (BinaryFourGluingLifetime.descriptorWithTrace_erasure input hC)
  (((⟨descriptor.1.1,
    by rw [hData]; exact BinaryFourParentCompiler.descriptor_canonical input hC,
    by rw [hData]; exact BinaryGluingSampler.descriptor_nonnegative input hC hAd⟩,descriptor.1.2),descriptor.2+4),produced.2)

def prepared (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) :
    (BinaryStoredSegmentProgram.Prepared 4 81 × Trace) × ℕ :=
  (preparedWithExtras input hC hAd).1

theorem preparedWithExtras_compat (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) :
    (preparedWithExtras input hC hAd).1 = prepared input hC hAd := rfl

theorem prepared_record (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) :
    prepared input hC hAd =
  let descriptor := BinaryFourGluingMeasured.descriptor input hC
  have hData : descriptor.1.1 = BinaryFourParentCompiler.descriptor input :=
    (BinaryFourGluingMeasured.descriptor_data input hC).trans
      (BinaryFourGluingLifetime.descriptorWithTrace_erasure input hC)
  ((⟨descriptor.1.1,
    by rw [hData]; exact BinaryFourParentCompiler.descriptor_canonical input hC,
    by rw [hData]; exact BinaryGluingSampler.descriptor_nonnegative input hC hAd⟩,descriptor.1.2),descriptor.2+4) := by
  simp only [prepared,preparedWithExtras,BinaryFourGluingMeasured.descriptorWithExtras_compat]

theorem prepared_data (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) :
    (prepared input hC hAd).1.1 = (BinaryFourGluingDrawLifetime.preparedWithTrace input hC hAd).1 := by
  simp only [prepared_record]
  unfold BinaryFourGluingDrawLifetime.preparedWithTrace
  simp only [BinaryFourGluingMeasured.descriptor_data]

set_option cleanup.letToHave false in
def runWithFactoryExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((BinaryPRGWordControllerSegment.Result store 4 × Trace) × ℕ) × ℕ) × ℕ :=
  let prepared := preparedWithExtras input hC hAd
  let held := prepared.1
  let produced := BinaryWordSegmentMeasured.runWithExtras store held.1.1 0 K scalar pc hp
  let drawn := produced.1
  ((((drawn.1.1,wrap 32 2 [held.1.2,drawn.1.2]),held.2+drawn.2+8),produced.2),prepared.2)

def runWithDrawExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerSegment.Result store 4 × Trace) × ℕ) × ℕ :=
  (runWithFactoryExtras store input hC hAd K scalar pc hp).1

theorem runWithFactoryExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K scalar pc hp).1 = runWithDrawExtras store input hC hAd K scalar pc hp := rfl

theorem runWithDrawExtras_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    runWithDrawExtras store input hC hAd K scalar pc hp =
  let held := prepared input hC hAd
  let produced := BinaryWordSegmentMeasured.runWithExtras store held.1.1 0 K scalar pc hp
  let drawn := produced.1
  (((drawn.1.1,wrap 32 2 [held.1.2,drawn.1.2]),held.2+drawn.2+8),produced.2) := by
  simp only [runWithDrawExtras,runWithFactoryExtras,BinaryFourGluingMeasured.descriptorWithExtras_compat,preparedWithExtras_compat]

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerSegment.Result store 4 × Trace) × ℕ :=
  (runWithDrawExtras store input hC hAd K scalar pc hp).1

theorem runWithDrawExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithDrawExtras store input hC hAd K scalar pc hp).1 = run store input hC hAd K scalar pc hp := rfl

theorem run_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    run store input hC hAd K scalar pc hp =
  let held := prepared input hC hAd
  let drawn := BinaryWordSegmentMeasured.run store held.1.1 0 K scalar pc hp
  ((drawn.1.1,wrap 32 2 [held.1.2,drawn.1.2]),held.2+drawn.2+8) := by
  simp only [run,runWithDrawExtras_record,BinaryWordSegmentMeasured.runWithExtras_compat]

theorem run_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K scalar pc hp).1.1 =
      (BinaryFourGluingDrawLifetime.runWithTrace store input hC hAd K scalar pc hp).1 := by
  simp only [run_record,BinaryFourGluingDrawLifetime.runWithTrace,prepared_data,BinaryWordSegmentMeasured.run_erases]

def workEnvelope (s K i cap : ℕ) : ℕ := BinaryFourGluingMeasured.workEnvelope s+
  BinaryWordSegmentMeasured.workEnvelope 4 81 (expressionHeightBudget s 36) K i cap+12
def envelope (s K i cap : ℕ) : ℕ := BinaryFourGluingMeasured.envelope s+
  BinaryWordSegmentLifetimeBound.envelope 4 81 (expressionHeightBudget s 36) K i cap+64

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : (1-source.p)*source.ell ≤ source.w)
    (hAd : BinaryGluingSampler.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K scalar pc hp).2 ≤ workEnvelope s K store.width store.cap.value ∧
      usage (run store input hC hAd K scalar pc hp).1.2 ≤ envelope s K store.width store.cap.value := by
  let held := prepared input hC hAd
  let drawn := BinaryWordSegmentMeasured.run store held.1.1 0 K scalar pc hp
  have hErasure := (prepared_data input hC hAd).trans (BinaryFourGluingDrawLifetime.preparedWithTrace_erasure input hC hAd)
  have hRef : held.1.1.table.Refines (source.gluingDescriptor hCase) := by
    dsimp only [held]
    rw [hErasure]
    exact BinaryFourParentCompiler.descriptor_refines input source hC hR hCase
  have hHeight := hH.gluingDescriptor (by omega : 2 ≤ s) hCase
  have hs36 : 3 ≤ expressionHeightBudget s 36 := hs.trans (expressionHeightBudget_ge_input s 36)
  have hFactory := BinaryFourGluingMeasured.descriptor_bounds input source hC hR hCase s hs hH
  have hDrawW := BinaryWordSegmentMeasured.run_work store held.1.1 (source.gluingDescriptor hCase) hRef
    (expressionHeightBudget s 36) hHeight.1 hHeight.2 0 K scalar pc hp
  have hDrawU := BinaryWordSegmentMeasured.run_usage store held.1.1 (source.gluingDescriptor hCase) hRef
    (expressionHeightBudget s 36) hs36 hHeight.1 hHeight.2 0 K scalar pc hp
  have hFactoryW : held.2 ≤ BinaryFourGluingMeasured.workEnvelope s+4 := by
    change (BinaryFourGluingMeasured.descriptor input hC).2+4 ≤ _
    omega
  have hFactoryU : usage held.1.2 ≤ BinaryFourGluingMeasured.envelope s := hFactory.2
  change drawn.2 ≤ _ at hDrawW
  change usage drawn.1.2 ≤ _ at hDrawU
  have hw := wrap_usage 32 2 [held.1.2,drawn.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change held.2+drawn.2+8 ≤ _ ∧ usage (wrap 32 2 [held.1.2,drawn.1.2]) ≤ _
  unfold workEnvelope envelope
  exact ⟨by omega,by omega⟩

theorem run_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K scalar pc hp).1.1.2.value ∧
      (run store input hC hAd K scalar pc hp).1.1.2.value ≤ store.cap.value :=
  BinaryWordSegmentMeasured.run_position store (prepared input hC hAd).1.1 0 K scalar pc hp

theorem old_branch_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryFourAdmissibility.Admissible input)
    (hGuard : BinaryFourParentCompiler.gluingCase input = true)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC (BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hGuard) K scalar pc hp).1.1 =
      BinaryPRGWordControllerFour.run store input hC hAd K outer scalar pc hp := by
  rw [run_data]
  exact BinaryFourGluingDrawLifetime.runWithTrace_old_branch store input hC hAd hGuard K outer scalar pc hp

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : (1-source.p)*source.ell ≤ source.w)
    (hAd : BinaryGluingSampler.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC hAd K scalar pc hp).1.2 steps ≤ borrowed+envelope s K store.width store.cap.value ∧
      framePeak ((run store input hC hAd K scalar pc hp).1.2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp).2 borrowed steps

end Blotto.BinaryFourGluingDrawMeasured
