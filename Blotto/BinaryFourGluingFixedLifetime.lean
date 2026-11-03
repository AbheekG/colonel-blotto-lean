import Blotto.BinaryScalarTape
import Blotto.BinaryFourGluingDrawLifetime
import Blotto.BinaryWordSegmentFixedLifetime

/-! One actual 81-slot gluing factory feeds both the optional draw and its
lower fallback. Fixed execution preserves the original row on every incoming
remaining word window and retains the returned absolute cursor. -/
namespace Blotto.BinaryFourGluingFixedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

private theorem old_sample (prepared : BinaryGluingSampler.Prepared) (K N : ℕ)
    (scalar : BinaryScalarTape K) (bits : Fin N → Bool) :
    (⟨prepared.table,prepared.canonical,prepared.nonnegative⟩ : BinaryStoredSegmentProgram.Prepared 4 81).sample
      0 K N scalar bits = prepared.fixedSample K N scalar bits := by
  unfold BinaryStoredSegmentProgram.Prepared.sample BinaryStoredSegmentProgram.Prepared.runIndexed
    BinaryStoredSegmentProgram.Prepared.selectIndexed BinaryStoredSegmentProgram.Prepared.lowerLeaf
    BinaryGluingSampler.Prepared.fixedSample BinaryGluingSampler.Prepared.runIndexed
    BinaryGluingSampler.Prepared.selectIndexed BinaryGluingSampler.Prepared.fallback
  dsimp only
  cases h : (BinaryCategoricalRun.runIndexed (0 : Fin 81) N bits
      (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative))
      0 (Nat.zero_le N)).1 <;> rfl

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace :=
  let prepared := BinaryFourGluingDrawLifetime.preparedWithTrace input hC hAd
  let drawn := BinaryWordSegmentFixedLifetime.runWithTrace store prepared.1 0 K scalar pc hp
  (drawn.1,wrap 32 2 [prepared.2,drawn.2])

theorem runWithTrace_window (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K scalar pc hp).1.1 =
      BinaryGluingSampler.fixedSample input hC hAd K (store.cap.value-pc.value) scalar
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value-pc.value) (by omega)) := by
  unfold runWithTrace
  dsimp only
  rw [BinaryWordSegmentFixedLifetime.runWithTrace_window,BinaryFourGluingDrawLifetime.preparedWithTrace_erasure]
  exact old_sample (BinaryGluingSampler.prepare input hC hAd) K _ scalar _

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC hAd K scalar pc hp).1.2.value ∧
      (runWithTrace store input hC hAd K scalar pc hp).1.2.value ≤ store.cap.value :=
  BinaryWordSegmentFixedLifetime.runWithTrace_position store
    (BinaryFourGluingDrawLifetime.preparedWithTrace input hC hAd).1 0 K scalar pc hp

theorem runWithTrace_cursor (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K scalar pc hp).1.2 =
      (BinaryPRGWordControllerSegment.run store (BinaryFourGluingDrawLifetime.oldPrepared input hC hAd) 0 K scalar pc hp).2 := by
  unfold runWithTrace
  dsimp only
  rw [BinaryWordSegmentFixedLifetime.runWithTrace_cursor,BinaryFourGluingDrawLifetime.preparedWithTrace_erasure]

def envelope (s K i b : ℕ) : ℕ :=
  BinaryFourGluingLifetime.envelope s+
    BinaryWordSegmentFixedLifetime.envelope 4 81 (expressionHeightBudget s 36) K i b+64

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (hAd : BinaryGluingSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC hAd K scalar pc hp).2 ≤ envelope s K store.width store.cap.value := by
  let prepared := BinaryFourGluingDrawLifetime.preparedWithTrace input hC hAd
  let drawn := BinaryWordSegmentFixedLifetime.runWithTrace store prepared.1 0 K scalar pc hp
  have hRef : prepared.1.table.Refines (source.gluingDescriptor hCase) := by
    dsimp only [prepared]
    rw [BinaryFourGluingDrawLifetime.preparedWithTrace_erasure]
    exact BinaryFourParentCompiler.descriptor_refines input source hC hR hCase
  have hHeight := hH.gluingDescriptor (by omega : 2 ≤ s) hCase
  have hFactory := BinaryFourGluingLifetime.descriptorWithTrace_usage input source hC hR hCase s hs hH
  have hDraw := BinaryWordSegmentFixedLifetime.runWithTrace_usage store prepared.1 0
    (source.gluingDescriptor hCase) hRef _ (hs.trans (expressionHeightBudget_ge_input s 36)) hHeight K scalar pc hp
  have hw := wrap_usage 32 2 [prepared.2,drawn.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (runWithTrace store input hC hAd K scalar pc hp).2 ≤ _ at hw
  change usage prepared.2 ≤ _ at hFactory
  change usage drawn.2 ≤ _ at hDraw
  unfold envelope
  omega

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (hAd : BinaryGluingSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC hAd K scalar pc hp).2 steps ≤ borrowed+envelope s K store.width store.cap.value ∧
      framePeak ((runWithTrace store input hC hAd K scalar pc hp).2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage store input source hC hR hCase hAd s hs hH K scalar pc hp) borrowed steps

end Blotto.BinaryFourGluingFixedLifetime
