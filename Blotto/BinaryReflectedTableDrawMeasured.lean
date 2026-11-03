import Blotto.BinaryReflectedEmissionMeasured
import Blotto.BinaryWordSegmentMeasured
import Blotto.BinaryReflectedTableDrawLifetime

/-! The actual shared-cap measured selector feeds one reached measured physical
point and reflected emission. Exact preceding optional output and absolute
cursor survive both selection exhaustion and successful emission. -/
namespace Blotto.BinaryReflectedTableDrawMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1200000

set_option cleanup.letToHave false in
def runWithExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerReflected.Result store × Trace) × ℕ) × ℕ :=
  let produced := BinaryWordSegmentMeasured.selectWithExtras store prepared (0 : Fin 18) pc hp
  let selected := produced.1
  match selected.1.1.1 with
  | none => ((((none,selected.1.1.2),wrap 24 2 [selected.1.2]),selected.2+4),produced.2)
  | some slot =>
      let result := BinaryReflectedEmissionMeasured.sampleWithExtras input prepared.table slot K scalar
      let emitted := result.1
      ((((some emitted.1.1,selected.1.1.2),wrap 32 2 [selected.1.2,emitted.1.2]),selected.2+emitted.2+8),produced.2+result.2)

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerReflected.Result store × Trace) × ℕ :=
  (runWithExtras store input prepared K scalar pc hp).1

theorem runWithExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)  :
    (runWithExtras store input prepared K scalar pc hp).1 = run store input prepared K scalar pc hp := rfl

theorem run_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)  :
    run store input prepared K scalar pc hp =
  let selected := BinaryWordSegmentMeasured.select store prepared (0 : Fin 18) pc hp
  match selected.1.1.1 with
  | none => (((none,selected.1.1.2),wrap 24 2 [selected.1.2]),selected.2+4)
  | some slot =>
      let emitted := BinaryReflectedEmissionMeasured.sample input prepared.table slot K scalar
      (((some emitted.1.1,selected.1.1.2),wrap 32 2 [selected.1.2,emitted.1.2]),selected.2+emitted.2+8) := by
  simp only [run,runWithExtras,BinaryWordSegmentMeasured.selectWithExtras_compat]
  cases h : (BinaryWordSegmentMeasured.select store prepared (0 : Fin 18) pc hp).1.1.1 with
  | none => simp only [h]
  | some slot => simp only [h,BinaryReflectedEmissionMeasured.sampleWithExtras_compat]


theorem run_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input prepared K scalar pc hp).1.1 = (BinaryReflectedTableDrawLifetime.runWithTrace store input prepared K scalar pc hp).1 := by
  simp only [run_record,BinaryReflectedTableDrawLifetime.runWithTrace,BinaryWordSegmentMeasured.select_erases,
    BinaryReflectedEmissionMeasured.sample_data]
  cases (BinaryWordSegmentLifetime.selectWithTrace store prepared (0 : Fin 18) pc hp).1.1 <;> rfl

theorem run_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input prepared K scalar pc hp).1.1.2.value ∧
      (run store input prepared K scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_data]
  exact BinaryReflectedTableDrawLifetime.runWithTrace_position store input prepared K scalar pc hp

def workEnvelope (s K i cap : ℕ) : ℕ := BinaryWordSegmentMeasured.selectionPrice 18 s i cap+BinaryReflectedEmissionMeasured.workEnvelope s K+8

def envelope (s K i cap : ℕ) : ℕ := BinaryWordSegmentLifetimeBound.selectionEnvelope 18 s i cap+BinaryReflectedEmissionMeasured.envelope s K+64

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (source : RationalSegmentLottery 3 18) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s)
    (hLengths : ∀ j,RationalHeight (value ((BinaryReflectedFourSetup.originalLengths input).read j)) s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input prepared K scalar pc hp).2 ≤ workEnvelope s K store.width store.cap.value ∧
      usage (run store input prepared K scalar pc hp).1.2 ≤ envelope s K store.width store.cap.value := by
  let selected := BinaryWordSegmentMeasured.select store prepared (0 : Fin 18) pc hp
  have hSelected : selected.2 ≤ BinaryWordSegmentMeasured.selectionPrice 18 s store.width store.cap.value ∧
      usage selected.1.2 ≤ BinaryWordSegmentLifetimeBound.selectionEnvelope 18 s store.width store.cap.value :=
    ⟨BinaryWordSegmentMeasured.select_work store prepared source hR s hHeight.1 (0 : Fin 18) pc hp,
      by rw [BinaryWordSegmentMeasured.select_erases]; exact BinaryWordSegmentLifetimeBound.selectWithTrace_usage store prepared source hR s hHeight.1 (0 : Fin 18) pc hp⟩
  have hEndpoint : ∀ slot j,RationalHeight (value ((prepared.table.P.read slot).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) s := by
    intro slot j; rw [hR.2.1 slot j,hR.2.2 slot j]; exact hHeight.2 slot j
  rw [run_record]
  dsimp only
  cases h : selected.1.1.1 with
  | none =>
      have hw := wrap_usage 24 2 [selected.1.2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change selected.2+4 ≤ _ ∧ usage (wrap 24 2 [selected.1.2]) ≤ _
      unfold workEnvelope envelope; exact ⟨by omega,by omega⟩
  | some slot =>
      have hEmitted := BinaryReflectedEmissionMeasured.sample_bounds input hC prepared.table prepared.canonical s hs hEndpoint hLengths slot K scalar
      have hw := wrap_usage 32 2 [selected.1.2,(BinaryReflectedEmissionMeasured.sample input prepared.table slot K scalar).1.2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change selected.2+(BinaryReflectedEmissionMeasured.sample input prepared.table slot K scalar).2+8 ≤ _ ∧ usage (wrap 32 2 [selected.1.2,_]) ≤ _
      unfold workEnvelope envelope; exact ⟨by omega,by omega⟩

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (source : RationalSegmentLottery 3 18) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s)
    (hLengths : ∀ j,RationalHeight (value ((BinaryReflectedFourSetup.originalLengths input).read j)) s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input prepared K scalar pc hp).1.2 steps ≤ borrowed+envelope s K store.width store.cap.value ∧
      framePeak ((run store input prepared K scalar pc hp).1.2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input hC prepared source hR s hs hHeight hLengths K scalar pc hp).2 borrowed steps

end Blotto.BinaryReflectedTableDrawMeasured
