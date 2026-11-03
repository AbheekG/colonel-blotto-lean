import Blotto.BinaryFourSmallFixedMeasured
import Blotto.BinaryFourGluingFixedMeasured
import Blotto.BinaryFourGuardMeasured
import Blotto.BinaryFourOrderedFixedLifetime

/-! One actual measured ordered-four guard selects only the reached measured
fixed gluing or small-root draw, including its deterministic exhaustion fallback. Original six-field heights derive the complete
source-work and retained-prefix bounds. Native model pricing remains separate. -/
namespace Blotto.BinaryFourOrderedFixedMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1200000

def join (store : BinarySeedLookupTree.Store) (guard : (Bool × Trace) × ℕ)
    (drawn : ((FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace) × ℕ) : ((FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace) × ℕ :=
  ((drawn.1.1,wrap 32 2 [guard.1.2,drawn.1.2]),guard.2+drawn.2+8)

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace) × ℕ :=
  let guard := BinaryFourGuardMeasured.guard input
  if hg : guard.1.1 = true then
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hg
    join store guard (BinaryFourGluingFixedMeasured.run store input hC
      (BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hOld) K scalar pc hp)
  else
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hg
    join store guard (BinaryFourSmallFixedMeasured.run store input hC (BinaryFourAdmissibility.small_guard input hC hAd hOld) K outer scalar pc hp)

theorem run_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1 = (BinaryFourOrderedFixedLifetime.runWithTrace store input hC hAd K outer scalar pc hp).1 := by
  simp only [run,join,BinaryFourOrderedFixedLifetime.runWithTrace,BinaryFourGuardMeasured.guard_erases,
    BinaryFourGluingFixedMeasured.run_data,BinaryFourSmallFixedMeasured.run_data]
  split <;> rfl

theorem run_window (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1.1 =
      BinaryFourSampler.fixedSample input hC hAd K (store.cap.value-pc.value) outer scalar
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value-pc.value) (by omega)) := by
  rw [run_data]
  exact BinaryFourOrderedFixedLifetime.runWithTrace_window store input hC hAd K outer scalar pc hp


def workEnvelope (s K i cap : ℕ) : ℕ := BinaryFourGuardMeasured.workEnvelope s+
  BinaryFourGluingFixedMeasured.workEnvelope s K i cap+BinaryFourSmallFixedMeasured.workEnvelope s K i cap+8

def envelope (s K i cap : ℕ) : ℕ := BinaryFourGuardLifetime.envelope s+
  BinaryFourGluingFixedMeasured.envelope s K i cap+BinaryFourSmallFixedMeasured.envelope s K i cap+128

theorem join_bounds (store : BinarySeedLookupTree.Store) (guard : (Bool × Trace) × ℕ)
    (drawn : ((FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace) × ℕ) (G D U F : ℕ)
    (hg : guard.2 ≤ G ∧ usage guard.1.2 ≤ U) (hd : drawn.2 ≤ D ∧ usage drawn.1.2 ≤ F) :
    (join store guard drawn).2 ≤ G+D+8 ∧ usage (join store guard drawn).1.2 ≤ U+F+64 := by
  have hw := wrap_usage 32 2 [guard.1.2,drawn.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change guard.2+drawn.2+8 ≤ _ ∧ usage (wrap 32 2 [guard.1.2,drawn.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourAdmissibility.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).2 ≤ workEnvelope s K store.width store.cap.value ∧
      usage (run store input hC hAd K outer scalar pc hp).1.2 ≤ envelope s K store.width store.cap.value := by
  let guard := BinaryFourGuardMeasured.guard input
  have hInputH := BinaryFourNativeOrderWork.input_height_of_refines input source hR s hH
  have hGuard : guard.2 ≤ BinaryFourGuardMeasured.workEnvelope s ∧ usage guard.1.2 ≤ BinaryFourGuardLifetime.envelope s :=
    ⟨BinaryFourGuardMeasured.guard_work input hC s hs hInputH,
      by rw [BinaryFourGuardMeasured.guard_erases]; exact BinaryFourGuardLifetime.guardWithTrace_usage input hC s hs hInputH⟩
  unfold run
  dsimp only
  split
  · rename_i hSelected
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hSelected
    have hCase := (BinaryFourParentCompiler.gluingCase_iff input source hC hR).mp hOld
    let branchAd := BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hOld
    have hDraw := BinaryFourGluingFixedMeasured.run_bounds store input source hC hR hCase branchAd s hs hH K scalar pc hp
    have hResult := join_bounds store guard _ _ _ _ _ hGuard hDraw
    exact ⟨hResult.1.trans (by unfold workEnvelope; omega),hResult.2.trans (by unfold envelope; omega)⟩
  · rename_i hSelected
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hSelected
    have hCase : source.w < (1-source.p)*source.ell := lt_of_not_ge (fun h => hOld ((BinaryFourParentCompiler.gluingCase_iff input source hC hR).mpr h))
    let branchAd := BinaryFourAdmissibility.small_guard input hC hAd hOld
    have hDraw := BinaryFourSmallFixedMeasured.run_bounds store input source hC hR hCase branchAd s hs hH K outer scalar pc hp
    have hResult := join_bounds store guard _ _ _ _ _ hGuard hDraw
    exact ⟨hResult.1.trans (by unfold workEnvelope; omega),hResult.2.trans (by unfold envelope; omega)⟩

theorem run_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K outer scalar pc hp).1.1.2.value ∧ (run store input hC hAd K outer scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_data]; exact BinaryFourOrderedFixedLifetime.runWithTrace_position store input hC hAd K outer scalar pc hp

theorem run_cursor (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1.2 =
      (BinaryPRGWordControllerFour.run store input hC hAd K outer scalar pc hp).2 := by
  rw [run_data]
  exact BinaryFourOrderedFixedLifetime.runWithTrace_cursor store input hC hAd K outer scalar pc hp

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourAdmissibility.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC hAd K outer scalar pc hp).1.2 steps ≤ borrowed+envelope s K store.width store.cap.value ∧
      framePeak ((run store input hC hAd K outer scalar pc hp).1.2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp).2 borrowed steps

end Blotto.BinaryFourOrderedFixedMeasured
