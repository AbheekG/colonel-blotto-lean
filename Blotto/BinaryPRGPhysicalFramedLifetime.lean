import Blotto.BinaryScalarTape
import Blotto.BinaryPhysicalOutputLifetime
import Blotto.BinaryPRGHeapFramedLifetime

/-! The actual prepared PRG draw now hands its returned normalized row to
physical heap/slot reads, Boolean indices, scaling and direct tape framing.
The one native row-to-list projection reserves its copied source list and
control frames; native reference-bit transport remains a model boundary. -/
namespace Blotto.BinaryPRGPhysicalFramedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapFixedProperties
set_option maxHeartbeats 3000000

theorem table_list {n : ℕ} {α : Type*} (table : FixedArrayTable n α) : List.ofFn table.read = table.data.toList := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,Array.length_toList,table.size]
  · intro i hi hi'
    simp only [List.getElem_ofFn,Array.getElem_toList,FixedArrayTable.read]

theorem output_table_state {n : ℕ} (budget : SignedWord) (header : List Bool) (row : FixedArrayTable n SignedWord) :
    (BinaryPhysicalOutputLifetime.outputWithTrace budget header row.data.toList).1 =
      BinaryQuadraticOutputLifetime.outputData budget header row := by
  rw [BinaryPhysicalOutputLifetime.output_state,← table_list row]
  simp only [BinaryQuadraticOutputLifetime.outputData,BinaryPhysicalRowOutput.scaledWords,List.map_ofFn]
  congr 2
  congr 1
  funext j
  simp only [BinaryQuadraticOutputLifetime.scaleData,FixedArrayTable.read_ofFn,Function.comp_def]

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) :
    (List Bool × FixedBinaryWord store.width) × Trace :=
  let drawn := BinaryPRGHeapFixedLifetime.runWithTrace store request rich K outer scalar
  let output := BinaryPhysicalOutputLifetime.outputWithTrace request.prepared.original.a header.bytes drawn.1.1.data.toList
  ((output.1,drawn.1.2),wrapList n 32 (n+2) [drawn.2,output.2])

theorem run_state {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) :
    (runWithTrace store request rich K outer scalar header).1 =
      (BinaryPRGHeapFramedLifetime.runWithTrace store request rich K outer scalar header).1 := by
  simp only [runWithTrace,BinaryPRGHeapFramedLifetime.runWithTrace,output_table_state,
    BinaryQuadraticOutputLifetime.outputWithTrace_erases]

theorem run_bytes {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) :
    (runWithTrace store request rich K outer scalar header).1.1 =
      BinaryStoredRowFrame.row (BinaryPRGWordControllerRequest.originalFixedSample store request rich K outer scalar) := by
  rw [run_state]
  exact BinaryPRGHeapFramedLifetime.runWithTrace_bytes store request rich K outer scalar header

theorem run_cursor {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) :
    (runWithTrace store request rich K outer scalar header).1.2 =
      (BinaryPRGWordControllerRequest.run store request rich K outer scalar).2 := by
  rw [run_state]
  exact BinaryPRGHeapFramedLifetime.runWithTrace_cursor store request rich K outer scalar header

noncomputable def envelope {n : ℕ} (request : BinaryPRGRequest.Request n) (K i b header : ℕ) : ℕ :=
  BinaryPRGHeapFramedLifetime.envelope request K i b header+
    BinaryPhysicalOutputLifetime.bound n (wordWidth request K) header+128

theorem run_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) :
    usage (runWithTrace store request rich K outer scalar header).2 ≤
      envelope request K store.width store.cap.value header.bytes.length := by
  let drawn := BinaryPRGHeapFixedLifetime.runWithTrace store request rich K outer scalar
  have hd := BinaryPRGHeapFixedLifetime.runWithTrace_usage store request rich K outer scalar
  have hRows : ∀ word ∈ drawn.1.1.data.toList,BinaryRationalOpcode.Valid word ∧ width word ≤ wordWidth request K := by
    rw [← table_list drawn.1.1]
    intro word hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact ⟨(BinaryPRGHeapFixedLifetime.runWithTrace_canonical store request rich K outer scalar j).1,
      row_width store request rich K outer scalar j⟩
  have ho := BinaryPhysicalOutputLifetime.output_usage request.prepared.original.a header.bytes drawn.1.1.data.toList
    request.valid.2.1.1.1 (wordWidth request K) (scale_width request K) hRows
  have hLength : drawn.1.1.data.toList.length = n := by rw [Array.length_toList,drawn.1.1.size]
  rw [hLength] at ho
  have hw := wrapList_usage n 32 (n+2) [drawn.2,
    (BinaryPhysicalOutputLifetime.outputWithTrace request.prepared.original.a header.bytes drawn.1.1.data.toList).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (runWithTrace store request rich K outer scalar header).2 ≤ _ at hw
  change usage drawn.2 ≤ _ at hd
  have hN : 2*n ≤ 2*(n+1)^2 := by nlinarith
  unfold envelope BinaryPRGHeapFramedLifetime.envelope BinaryQuadraticOutputLifetime.bound BinaryQuadraticOutputLifetime.frames
  omega

theorem all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (header : BinaryPRGHeaderFrame.Header n) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store request rich K outer scalar header).2 steps ≤
        borrowed+envelope request K store.width store.cap.value header.bytes.length ∧
      framePeak ((runWithTrace store request rich K outer scalar header).2.take steps) ≤
        envelope request K store.width store.cap.value header.bytes.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_usage store request rich K outer scalar header) borrowed steps

end Blotto.BinaryPRGPhysicalFramedLifetime
