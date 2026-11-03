import Blotto.BinaryScalarTape
import Blotto.BinaryFourGluingLifetime
import Blotto.BinaryWordSegmentLifetimeBound
import Blotto.BinaryGluingSampler
import Blotto.BinaryPRGWordControllerFour

/-! The actually built 81-slot gluing descriptor feeds the Boolean-PC
categorical/point draw. Proof-only admissibility fields do not rerun a factory. -/
namespace Blotto.BinaryFourGluingDrawLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def preparedWithTrace (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryGluingSampler.Admissible input) :
    BinaryStoredSegmentProgram.Prepared 4 81 × Trace :=
  let descriptor := BinaryFourGluingLifetime.descriptorWithTrace input hC
  (⟨descriptor.1,
    by rw [BinaryFourGluingLifetime.descriptorWithTrace_erasure]; exact BinaryFourParentCompiler.descriptor_canonical input hC,
    by rw [BinaryFourGluingLifetime.descriptorWithTrace_erasure]; exact BinaryGluingSampler.descriptor_nonnegative input hC hAd⟩,
    descriptor.2)

def oldPrepared (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryGluingSampler.Admissible input) : BinaryStoredSegmentProgram.Prepared 4 81 :=
  let old := BinaryGluingSampler.prepare input hC hAd
  ⟨old.table,old.canonical,old.nonnegative⟩

private theorem prepared_eq {p q : BinaryStoredSegmentProgram.Prepared 4 81}
    (h : p.table = q.table) : p = q := by
  cases p with
  | mk pt pc pn =>
    cases q with
    | mk qt qc qn =>
      dsimp only at h
      cases h
      rfl

theorem preparedWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryGluingSampler.Admissible input) :
    (preparedWithTrace input hC hAd).1 = oldPrepared input hC hAd := by
  apply prepared_eq
  simp only [preparedWithTrace,oldPrepared,BinaryGluingSampler.prepare]
  exact BinaryFourGluingLifetime.descriptorWithTrace_erasure input hC

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerSegment.Result store 4 × Trace :=
  let prepared := preparedWithTrace input hC hAd
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared.1 0 K scalar pc hp
  (drawn.1,wrap 32 2 [prepared.2,drawn.2])

theorem runWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K scalar pc hp).1 =
      BinaryPRGWordControllerSegment.run store (oldPrepared input hC hAd) 0 K scalar pc hp := by
  unfold runWithTrace
  dsimp only
  rw [BinaryWordSegmentLifetime.runWithTrace_erasure,preparedWithTrace_erasure]

theorem sampler_admissible (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input)
    (hGuard : BinaryFourParentCompiler.gluingCase input = true) :
    BinaryGluingSampler.Admissible input := by
  obtain ⟨source,hR⟩ := hAd
  exact ⟨source,hR,(BinaryFourParentCompiler.gluingCase_iff input source hC hR).mp hGuard⟩

theorem runWithTrace_old_branch (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryFourAdmissibility.Admissible input)
    (hGuard : BinaryFourParentCompiler.gluingCase input = true)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC (sampler_admissible input hC hAd hGuard)
      K scalar pc hp).1 =
      BinaryPRGWordControllerFour.run store input hC hAd K outer scalar pc hp := by
  rw [runWithTrace_erasure]
  unfold BinaryPRGWordControllerFour.run
  simp only [hGuard, dite_true]
  rfl

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC hAd K scalar pc hp).1.2.value ∧
      (runWithTrace store input hC hAd K scalar pc hp).1.2.value ≤ store.cap.value :=
  BinaryWordSegmentLifetime.runWithTrace_position store (preparedWithTrace input hC hAd).1 0 K scalar pc hp

def envelope (s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryFourGluingLifetime.envelope s +
    BinaryWordSegmentLifetimeBound.envelope 4 81 (expressionHeightBudget s 36) K indexWidth seedCap + 64

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (hAd : BinaryGluingSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC hAd K scalar pc hp).2 ≤
      envelope s K store.width store.cap.value := by
  let prepared := preparedWithTrace input hC hAd
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared.1 0 K scalar pc hp
  have hErasure := preparedWithTrace_erasure input hC hAd
  have hRef : prepared.1.table.Refines (source.gluingDescriptor hCase) := by
    dsimp only [prepared]
    rw [hErasure]
    exact BinaryFourParentCompiler.descriptor_refines input source hC hR hCase
  have hHeight := hH.gluingDescriptor (by omega : 2 ≤ s) hCase
  have hs36 : 3 ≤ expressionHeightBudget s 36 := hs.trans (expressionHeightBudget_ge_input s 36)
  have hFactory := BinaryFourGluingLifetime.descriptorWithTrace_usage input source hC hR hCase s hs hH
  have hDraw := BinaryWordSegmentLifetimeBound.runWithTrace_usage store prepared.1
    (source.gluingDescriptor hCase) hRef (expressionHeightBudget s 36) hs36 hHeight.1 hHeight.2
    0 K scalar pc hp
  change usage prepared.2 ≤ _ at hFactory
  change usage drawn.2 ≤ _ at hDraw
  have hw := wrap_usage 32 2 [prepared.2,drawn.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [prepared.2,drawn.2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (hAd : BinaryGluingSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC hAd K scalar pc hp).2 steps ≤
      borrowed + envelope s K store.width store.cap.value ∧
    framePeak ((runWithTrace store input hC hAd K scalar pc hp).2.take steps) ≤
      envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store input source hC hR hCase hAd s hs hH K scalar pc hp) borrowed steps

end Blotto.BinaryFourGluingDrawLifetime
