import Blotto.BinaryScalarTape
import Blotto.BinaryFourSmallFixedLifetime
import Blotto.BinaryFourGluingFixedLifetime
import Blotto.BinaryFourGuardLifetime

/-! One traced guard selects the complete fixed gluing or small-root producer,
including the selected lower exhaustion fallback. The original bounded sampler
row is preserved on every remaining input word window. -/
namespace Blotto.BinaryFourOrderedFixedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryFourAdmissibility.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : (FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace :=
  let guard := BinaryFourGuardLifetime.guardWithTrace input
  if hg : guard.1 = true then
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hg
    let drawn := BinaryFourGluingFixedLifetime.runWithTrace store input hC
      (BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hOld) K scalar pc hp
    (drawn.1,wrap 32 2 [guard.2,drawn.2])
  else
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hg
    let drawn := BinaryFourSmallFixedLifetime.runWithTrace store input hC
      (BinaryFourAdmissibility.small_guard input hC hAd hOld) K outer scalar pc hp
    (drawn.1,wrap 32 2 [guard.2,drawn.2])

theorem runWithTrace_window (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryFourAdmissibility.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K outer scalar pc hp).1.1 =
      BinaryFourSampler.fixedSample input hC hAd K (store.cap.value-pc.value) outer scalar
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value-pc.value) (by omega)) := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hGuard
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hGuard
    rw [BinaryFourGluingFixedLifetime.runWithTrace_window]
    unfold BinaryFourSampler.fixedSample
    simp only [hOld,dite_true]
  · rename_i hGuard
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hGuard
    rw [BinaryFourSmallFixedLifetime.runWithTrace_window]
    unfold BinaryFourSampler.fixedSample
    simp only [hOld,Bool.false_eq_true,dite_false]

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryFourAdmissibility.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ∧
      (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ≤ store.cap.value := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hGuard
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hGuard
    exact BinaryFourGluingFixedLifetime.runWithTrace_position store input hC
      (BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hOld) K scalar pc hp
  · rename_i hGuard
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hGuard
    exact BinaryFourSmallFixedLifetime.runWithTrace_position store input hC
      (BinaryFourAdmissibility.small_guard input hC hAd hOld) K outer scalar pc hp

theorem runWithTrace_cursor (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryFourAdmissibility.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K outer scalar pc hp).1.2 =
      (BinaryPRGWordControllerFour.run store input hC hAd K outer scalar pc hp).2 := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hGuard
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hGuard
    rw [BinaryFourGluingFixedLifetime.runWithTrace_cursor]
    unfold BinaryPRGWordControllerFour.run
    simp only [hOld,dite_true]
    rfl
  · rename_i hGuard
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hGuard
    rw [BinaryFourSmallFixedLifetime.runWithTrace_erasure]
    unfold BinaryPRGWordControllerFour.run
    simp only [hOld,Bool.false_eq_true,dite_false]

def envelope (s K indexWidth seedCap remaining : ℕ) : ℕ :=
  BinaryFourGuardLifetime.envelope s + BinaryFourGluingFixedLifetime.envelope s K indexWidth seedCap +
    BinaryFourSmallFixedLifetime.envelope s K indexWidth seedCap remaining + 256

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hAd : BinaryFourAdmissibility.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC hAd K outer scalar pc hp).2 ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) := by
  let guard := BinaryFourGuardLifetime.guardWithTrace input
  have hGuard := BinaryFourGuardLifetime.guardWithTrace_usage input hC s hs
    (BinaryFourNativeOrderWork.input_height_of_refines input source hR s hH)
  change usage guard.2 ≤ _ at hGuard
  unfold runWithTrace
  dsimp only
  split
  · rename_i hSelected
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hSelected
    have hCase := (BinaryFourParentCompiler.gluingCase_iff input source hC hR).mp hOld
    let branchAd := BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hOld
    have hDraw := BinaryFourGluingFixedLifetime.runWithTrace_usage store input source hC hR hCase branchAd
      s hs hH K scalar pc hp
    have hw := wrap_usage 32 2 [guard.2,
      (BinaryFourGluingFixedLifetime.runWithTrace store input hC branchAd K scalar pc hp).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [guard.2,
      (BinaryFourGluingFixedLifetime.runWithTrace store input hC branchAd K scalar pc hp).2]) ≤ _
    unfold envelope
    omega
  · rename_i hSelected
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hSelected
    have hCase : source.w < (1-source.p)*source.ell :=
      lt_of_not_ge (fun h => hOld ((BinaryFourParentCompiler.gluingCase_iff input source hC hR).mpr h))
    let branchAd := BinaryFourAdmissibility.small_guard input hC hAd hOld
    have hDraw := BinaryFourSmallFixedLifetime.runWithTrace_usage store input source hC hR hCase branchAd
      s hs hH K outer scalar pc hp
    have hw := wrap_usage 32 2 [guard.2,
      (BinaryFourSmallFixedLifetime.runWithTrace store input hC branchAd K outer scalar pc hp).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [guard.2,
      (BinaryFourSmallFixedLifetime.runWithTrace store input hC branchAd K outer scalar pc hp).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hAd : BinaryFourAdmissibility.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC hAd K outer scalar pc hp).2 steps ≤
      borrowed + envelope s K store.width store.cap.value (store.cap.value-pc.value) ∧
    framePeak ((runWithTrace store input hC hAd K outer scalar pc hp).2.take steps) ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store input source hC hR hAd s hs hH K outer scalar pc hp) borrowed steps

end Blotto.BinaryFourOrderedFixedLifetime
