import Blotto.BinaryLifetimeMapMeasured
import Blotto.BinaryWordObjectArrayMeasured
import Blotto.BinaryPRGCheckedPhysicalPreparationLifetime

/-! One measured entry projection feeds actual measured Boolean leaf-object
and pointer-slot allocation. Casts carry erased length proofs only. The
old physical store and trace are exact; native allocator/reference/observer
realisation remains separate from these source component bounds. -/
namespace Blotto.BinaryPRGNumericalPhysicalMapMeasured
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGCheckedPhysicalPreparationLifetime
set_option autoImplicit false

theorem cast_heap {m n : ℕ} (h : m = n) (store : BinaryWordObjectArray.Store m) :
    (castStore h store).heap = store.heap := by cases h; rfl

theorem cast_slots {m n : ℕ} (h : m = n) (store : BinaryWordObjectArray.Store m) :
    (castStore h store).slots = store.slots := by cases h; rfl

def prepare (entries : List (SignedWord × Trace)) : (BinaryWordObjectArray.Store entries.length × Trace) × ℕ :=
  let projected := BinaryLifetimeMapMeasured.project Prod.fst entries
  let allocated := BinaryWordObjectArrayMeasured.prepare projected.1.1
  have hSize : projected.1.1.length = entries.length := by
    rw [BinaryLifetimeMapMeasured.project_erases,BinaryLifetimeArray.mapDirectWithTrace_state,
      BinaryLifetimeArray.mapDirect_length]
  ((castStore hSize allocated.1.1,wrapList 1 32 2 [projected.1.2,allocated.1.2]),projected.2+allocated.2+8)

theorem prepare_erases (entries : List (SignedWord × Trace)) :
    (prepare entries).1 = BinaryPRGCheckedPhysicalPreparationLifetime.fixedPhysical entries.length entries rfl := by
  apply Prod.ext
  · apply BinaryWordObjectArray.Store.ext
    · simp only [prepare,BinaryPRGCheckedPhysicalPreparationLifetime.fixedPhysical,
        BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace,cast_heap,
        BinaryLifetimeMapMeasured.project_erases,BinaryWordObjectArrayMeasured.prepare_erases]
      exact congrArg (fun words : List SignedWord => (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.heap)
        (congrArg Prod.fst (BinaryLifetimeMapMeasured.project_erases Prod.fst entries))
    · simp only [prepare,BinaryPRGCheckedPhysicalPreparationLifetime.fixedPhysical,
        BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace,cast_slots,
        BinaryLifetimeMapMeasured.project_erases,BinaryWordObjectArrayMeasured.prepare_erases]
      exact congrArg (fun words : List SignedWord => (BinaryWordObjectArrayLifetime.prepareWithTrace words).1.slots)
        (congrArg Prod.fst (BinaryLifetimeMapMeasured.project_erases Prod.fst entries))
  · simp only [prepare,BinaryPRGCheckedPhysicalPreparationLifetime.fixedPhysical,
      BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace,
      BinaryLifetimeMapMeasured.project_erases,BinaryWordObjectArrayMeasured.prepare_erases]
    exact congrArg (fun words : List SignedWord => wrapList 1 32 2
      [(BinaryLifetimeArray.mapDirectWithTrace Prod.fst entries).2,
        (BinaryWordObjectArrayLifetime.prepareWithTrace words).2])
      (congrArg Prod.fst (BinaryLifetimeMapMeasured.project_erases Prod.fst entries))

def fixedPhysical (n : ℕ) (entries : List (SignedWord × Trace)) (hEntries : entries.length = n) :
    (BinaryWordObjectArray.Store n × Trace) × ℕ :=
  let prepared := prepare entries
  ((castStore hEntries prepared.1.1,prepared.1.2),prepared.2)

theorem fixedPhysical_erases (n : ℕ) (entries : List (SignedWord × Trace)) (hEntries : entries.length = n) :
    (fixedPhysical n entries hEntries).1 =
      BinaryPRGCheckedPhysicalPreparationLifetime.fixedPhysical n entries hEntries := by
  cases hEntries
  exact prepare_erases entries

theorem fixedPhysical_readback (n : ℕ) (entries : List (SignedWord × Trace)) (hEntries : entries.length = n)
    (index : List Bool) (j : Fin n) (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace (fixedPhysical n entries hEntries).1.1 index).1 =
      some ((BinaryLifetimeArray.fromEntries n entries hEntries).1.read j) := by
  rw [fixedPhysical_erases]
  exact BinaryPRGCheckedPhysicalPreparationLifetime.fixedPhysical_readback n entries hEntries index j hIndex

theorem prepare_work (entries : List (SignedWord × Trace)) :
    (prepare entries).2 ≤ BinaryWordObjectArrayLifetime.envelope (BinaryPRGNumericalPhysicalEntries.words entries)+
      4*entries.length+10 := by
  let projected := BinaryLifetimeMapMeasured.project Prod.fst entries
  have hp := BinaryLifetimeMapMeasured.project_work Prod.fst entries
  have ha := BinaryWordObjectArrayMeasured.prepare_bound projected.1.1
  have hData : projected.1.1 = BinaryPRGNumericalPhysicalEntries.words entries := by
    rw [BinaryLifetimeMapMeasured.project_erases]
    exact BinaryPRGNumericalPhysicalMapLifetime.projected_trace_words entries
  have hEnvelope := congrArg BinaryWordObjectArrayLifetime.workEnvelope hData
  rw [hEnvelope] at ha
  have he := PRGPhysicalArrayInterface.workEnvelope_le_source (BinaryPRGNumericalPhysicalEntries.words entries)
  change projected.2 = _ at hp
  change projected.2+(BinaryWordObjectArrayMeasured.prepare projected.1.1).2+8 ≤ _
  omega

theorem fixedPhysical_raw_work (L n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ L)
    (hWidth : ∀ word ∈ BinaryPRGNumericalPhysicalEntries.words entries,width word ≤ 9*L+22) :
    (fixedPhysical n entries hEntries).2 ≤ PRGPhysicalArrayInterface.preparationBound L+4*L+10 := by
  have h := prepare_work entries
  have he := BinaryPRGNumericalPhysicalEntries.physical_raw_envelope L n entries hEntries hn hWidth
  have hnEntries : entries.length ≤ L := hEntries.trans_le hn
  change (prepare entries).2 ≤ _
  omega

theorem prepare_usage (entries : List (SignedWord × Trace)) : usage (prepare entries).1.2 ≤
    BinaryWordObjectArrayLifetime.envelope (BinaryPRGNumericalPhysicalEntries.words entries)+2*entries.length+40 := by
  rw [prepare_erases]
  exact BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace_usage entries

end Blotto.BinaryPRGNumericalPhysicalMapMeasured
