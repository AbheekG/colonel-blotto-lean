import Blotto.BinaryScalarTape
import Blotto.BinaryFourSmallLifetime
import Blotto.BinaryFourGluingDrawLifetime
import Blotto.BinaryFourGuardLifetime

/-! One actual ordered-four guard selects the complete traced gluing or
small-root draw. Original six-field heights derive both branch reservations;
every optional failure and absolute cursor equals the previous controller. -/
namespace Blotto.BinaryFourOrderedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryFourAdmissibility.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerFour.Result store × Trace :=
  let guard := BinaryFourGuardLifetime.guardWithTrace input
  if hg : guard.1 = true then
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hg
    let drawn := BinaryFourGluingDrawLifetime.runWithTrace store input hC
      (BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hOld) K scalar pc hp
    (drawn.1,wrap 32 2 [guard.2,drawn.2])
  else
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hg
    let drawn := BinaryFourSmallLifetime.runWithTrace store input hC
      (BinaryFourAdmissibility.small_guard input hC hAd hOld) K outer scalar pc hp
    (drawn.1,wrap 32 2 [guard.2,drawn.2])

theorem runWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryFourAdmissibility.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerFour.run store input hC hAd K outer scalar pc hp := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hGuard
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hGuard
    exact BinaryFourGluingDrawLifetime.runWithTrace_old_branch store input hC hAd hOld K outer scalar pc hp
  · rename_i hGuard
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hGuard
    rw [BinaryFourSmallLifetime.runWithTrace_erasure]
    unfold BinaryPRGWordControllerFour.run
    simp only [hOld,Bool.false_eq_true,dite_false]

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryFourAdmissibility.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ∧
      (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ≤ store.cap.value := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerFour.run_position store input hC hAd K outer scalar pc hp

def envelope (s K indexWidth seedCap remaining : ℕ) : ℕ :=
  BinaryFourGuardLifetime.envelope s + BinaryFourGluingDrawLifetime.envelope s K indexWidth seedCap +
    BinaryFourSmallLifetime.envelope s K indexWidth seedCap remaining + 256

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
    have hDraw := BinaryFourGluingDrawLifetime.runWithTrace_usage store input source hC hR hCase branchAd
      s hs hH K scalar pc hp
    have hw := wrap_usage 32 2 [guard.2,
      (BinaryFourGluingDrawLifetime.runWithTrace store input hC branchAd K scalar pc hp).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [guard.2,
      (BinaryFourGluingDrawLifetime.runWithTrace store input hC branchAd K scalar pc hp).2]) ≤ _
    unfold envelope
    omega
  · rename_i hSelected
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC]
      exact hSelected
    have hCase : source.w < (1-source.p)*source.ell :=
      lt_of_not_ge (fun h => hOld ((BinaryFourParentCompiler.gluingCase_iff input source hC hR).mpr h))
    let branchAd := BinaryFourAdmissibility.small_guard input hC hAd hOld
    have hDraw := BinaryFourSmallLifetime.runWithTrace_usage store input source hC hR hCase branchAd
      s hs hH K outer scalar pc hp
    have hw := wrap_usage 32 2 [guard.2,
      (BinaryFourSmallLifetime.runWithTrace store input hC branchAd K outer scalar pc hp).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [guard.2,
      (BinaryFourSmallLifetime.runWithTrace store input hC branchAd K outer scalar pc hp).2]) ≤ _
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

end Blotto.BinaryFourOrderedLifetime
