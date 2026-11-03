import Blotto.BinaryFourGluingDrawMeasured
import Blotto.BinaryWordSegmentFixedMeasured
import Blotto.BinaryFourGluingFixedLifetime

/-! One actual measured gluing factory supplies a shared table to optional
selection/point work and reached deterministic lower fallback. Every incoming
word window yields the previous bounded sampler row and absolute cursor. -/
namespace Blotto.BinaryFourGluingFixedMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace) × ℕ :=
  let held := BinaryFourGluingDrawMeasured.prepared input hC hAd
  let drawn := BinaryWordSegmentFixedMeasured.run store held.1.1 0 K scalar pc hp
  ((drawn.1.1,wrap 32 2 [held.1.2,drawn.1.2]),held.2+drawn.2+8)

theorem run_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K scalar pc hp).1.1 = (BinaryFourGluingFixedLifetime.runWithTrace store input hC hAd K scalar pc hp).1 := by
  simp only [run,BinaryFourGluingFixedLifetime.runWithTrace,BinaryFourGluingDrawMeasured.prepared_data,BinaryWordSegmentFixedMeasured.run_erases]

def workEnvelope (s K i cap : ℕ) : ℕ := BinaryFourGluingMeasured.workEnvelope s+
  BinaryWordSegmentFixedMeasured.workEnvelope 4 81 (expressionHeightBudget s 36) K i cap+12

def envelope (s K i cap : ℕ) : ℕ := BinaryFourGluingMeasured.envelope s+
  BinaryWordSegmentFixedLifetime.envelope 4 81 (expressionHeightBudget s 36) K i cap+64

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : (1-source.p)*source.ell ≤ source.w)
    (hAd : BinaryGluingSampler.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K scalar pc hp).2 ≤ workEnvelope s K store.width store.cap.value ∧
      usage (run store input hC hAd K scalar pc hp).1.2 ≤ envelope s K store.width store.cap.value := by
  let held := BinaryFourGluingDrawMeasured.prepared input hC hAd
  let drawn := BinaryWordSegmentFixedMeasured.run store held.1.1 0 K scalar pc hp
  have hErasure := (BinaryFourGluingDrawMeasured.prepared_data input hC hAd).trans (BinaryFourGluingDrawLifetime.preparedWithTrace_erasure input hC hAd)
  have hRef : held.1.1.table.Refines (source.gluingDescriptor hCase) := by
    dsimp only [held]; rw [hErasure]; exact BinaryFourParentCompiler.descriptor_refines input source hC hR hCase
  have hHeight := hH.gluingDescriptor (by omega : 2 ≤ s) hCase
  have hs36 : 3 ≤ expressionHeightBudget s 36 := hs.trans (expressionHeightBudget_ge_input s 36)
  have hFactory := BinaryFourGluingMeasured.descriptor_bounds input source hC hR hCase s hs hH
  have hDraw := BinaryWordSegmentFixedMeasured.run_bounds store held.1.1 0 (source.gluingDescriptor hCase) hRef _ hs36 hHeight K scalar pc hp
  change drawn.2 ≤ _ ∧ usage drawn.1.2 ≤ _ at hDraw
  have hFactoryW : held.2 ≤ BinaryFourGluingMeasured.workEnvelope s+4 := by
    change (BinaryFourGluingMeasured.descriptor input hC).2+4 ≤ _; omega
  have hFactoryU : usage held.1.2 ≤ BinaryFourGluingMeasured.envelope s := hFactory.2
  have hw := wrap_usage 32 2 [held.1.2,drawn.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change held.2+drawn.2+8 ≤ _ ∧ usage (wrap 32 2 [held.1.2,drawn.1.2]) ≤ _
  unfold workEnvelope envelope
  exact ⟨by omega,by omega⟩

theorem run_window (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K scalar pc hp).1.1.1 = BinaryGluingSampler.fixedSample input hC hAd K (store.cap.value-pc.value) scalar
      (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value (store.cap.value-pc.value) (by omega)) := by
  rw [run_data]
  exact BinaryFourGluingFixedLifetime.runWithTrace_window store input hC hAd K scalar pc hp

theorem run_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K scalar pc hp).1.1.2.value ∧ (run store input hC hAd K scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_data]
  exact BinaryFourGluingFixedLifetime.runWithTrace_position store input hC hAd K scalar pc hp

theorem run_cursor (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K scalar pc hp).1.1.2 =
      (BinaryPRGWordControllerSegment.run store (BinaryFourGluingDrawLifetime.oldPrepared input hC hAd) 0 K scalar pc hp).2 := by
  rw [run_data]
  exact BinaryFourGluingFixedLifetime.runWithTrace_cursor store input hC hAd K scalar pc hp

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : (1-source.p)*source.ell ≤ source.w)
    (hAd : BinaryGluingSampler.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC hAd K scalar pc hp).1.2 steps ≤ borrowed+envelope s K store.width store.cap.value ∧
      framePeak ((run store input hC hAd K scalar pc hp).1.2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp).2 borrowed steps

end Blotto.BinaryFourGluingFixedMeasured
