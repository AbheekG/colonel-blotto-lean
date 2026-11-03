import Blotto.BinaryHeapReadMeasured
import Blotto.BinaryPRGHeapPackedLifetime
import Blotto.BinarySeedCursorMeasured

/-! One actual physical tape lookup, including the reached reads and address
reversal, returns its value/trace/work together. Old heap work charges and
trace are exact. Logical trees occur only in erased validity proofs; native
observer/reference/allocator realisation remains separate. -/
namespace Blotto.BinaryHeapPackedReadMeasured
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace BinaryTraceDepth
open BinaryPRGWordStoreHeapMachine (Charge)
open BinaryPRGHeapPackedStore (Packed)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def lookupAt : List Bool → Pointer → List Bool → List Bool → ℕ → (Option SignedWord × Trace) × Charge
  | tape,pointer,[],_,traceDepth =>
      let found := BinaryHeapReadMeasured.readAt tape pointer (traceDepth+1)
      ((match found.1.1 with | some (.leaf word) => some word | _ => none,
        .frames (traceDepth+2)::.arrayAllocation 8::found.1.2),found.2.add ⟨2,4⟩)
  | tape,pointer,_::ruler,address,traceDepth =>
      let found := BinaryHeapReadMeasured.readAt tape pointer (traceDepth+1)
      match found.1.1 with
      | some (.branch left right) =>
          let later := if address.headD false then lookupAt tape right ruler address.tail (traceDepth+1) else lookupAt tape left ruler address.tail (traceDepth+1)
          ((later.1.1,.frames (traceDepth+2)::.arrayAllocation 8::(found.1.2++later.1.2)),found.2.add (later.2.add ⟨4,4⟩))
      | _ => ((none,.frames (traceDepth+2)::.arrayAllocation 8::found.1.2),found.2.add ⟨2,4⟩)


theorem lookupAt_erases (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) (traceDepth : ℕ) :
    (lookupAt tape pointer ruler address traceDepth).1 =
      ((BinaryPRGHeapAccessLifetime.lookupWithTrace tape pointer ruler address).1,
        under traceDepth (BinaryPRGHeapAccessLifetime.lookupWithTrace tape pointer ruler address).2) := by
  induction ruler generalizing pointer address traceDepth with
  | nil =>
      simp only [lookupAt,BinaryPRGHeapAccessLifetime.lookupWithTrace,BinaryHeapReadMeasured.readAt_erases,
        under_append,under_compose]
      rfl
  | cons bit ruler ih =>
      simp only [lookupAt,BinaryPRGHeapAccessLifetime.lookupWithTrace,BinaryHeapReadMeasured.readAt_erases]
      cases (BinaryPRGHeapAllocationLifetime.readWithTrace tape pointer).1 with
      | none => simp only [under_append,under_compose]; rfl
      | some cell => cases cell with
        | leaf word => simp only [under_append,under_compose]; rfl
        | branch left right => cases address.headD false <;>
            simp only [Bool.false_eq_true,ite_false,ite_true,ih,under_append,under_compose,List.append_assoc] <;> rfl

def lookup (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) :
    (Option SignedWord × Trace) × Charge := lookupAt tape pointer ruler address 0

theorem lookup_erases (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) :
    (lookup tape pointer ruler address).1 = BinaryPRGHeapAccessLifetime.lookupWithTrace tape pointer ruler address := by
  rw [lookup,lookupAt_erases,under_zero]

theorem lookupAt_data (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) (traceDepth : ℕ) :
    (lookupAt tape pointer ruler address traceDepth).1.1 =
      (BinaryPRGWordStoreHeapMachine.lookupWithWork tape pointer ruler address).1 := by
  rw [lookupAt_erases]
  exact BinaryPRGHeapAccessLifetime.lookupWithTrace_erasure tape pointer ruler address

theorem lookup_data (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) :
    (lookup tape pointer ruler address).1.1 = (BinaryPRGWordStoreHeapMachine.lookupWithWork tape pointer ruler address).1 := by
  rw [lookup_erases]
  exact BinaryPRGHeapAccessLifetime.lookupWithTrace_erasure tape pointer ruler address

theorem lookupAt_charge (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) (traceDepth : ℕ) :
    (lookupAt tape pointer ruler address traceDepth).2 = (BinaryPRGWordStoreHeapMachine.lookupWithWork tape pointer ruler address).2 := by
  induction ruler generalizing pointer address traceDepth with
  | nil => simp only [lookupAt,BinaryPRGWordStoreHeapMachine.lookupWithWork,BinaryHeapReadMeasured.readAt_erases,
    BinaryPRGHeapAllocationLifetime.readWithTrace_erasure,BinaryHeapReadMeasured.readAt_charge]
  | cons bit ruler ih =>
      simp only [lookupAt,BinaryPRGWordStoreHeapMachine.lookupWithWork,BinaryHeapReadMeasured.readAt_erases,
    BinaryPRGHeapAllocationLifetime.readWithTrace_erasure,BinaryHeapReadMeasured.readAt_charge]
      cases (BinaryPRGWordStoreHeapMachine.readWithWork tape pointer).1 with
      | none => rfl
      | some cell => cases cell with
        | leaf word => rfl
        | branch left right => cases address.headD false <;>
            simp only [Bool.false_eq_true,ite_false,ite_true,ih]


theorem lookup_charge (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) :
    (lookup tape pointer ruler address).2 = (BinaryPRGWordStoreHeapMachine.lookupWithWork tape pointer ruler address).2 :=
  lookupAt_charge tape pointer ruler address 0

def readAt {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (traceDepth : ℕ) : (SignedWord × Trace) × ℕ :=
  let reversed := BinarySeedCursorMeasured.reverseAt address.bits [] (traceDepth+1)
  let executed := lookupAt data.heap.tape data.root data.ruler reversed.1.1 (traceDepth+1)
  have hSome : executed.1.1.isSome := by
    rw [lookupAt_data,BinarySeedCursorMeasured.reverseAt_erases,
      BinarySeedPreparationSpace.reverseWithTrace_result,List.reverseAux_eq,List.append_nil]
    obtain ⟨tree,hTree⟩ := data.realized
    rw [BinaryPRGWordStoreHeapMachine.lookupWithWork_erasure,
      lookup_realizes hTree data.ruler address.bits.reverse data.size (by rw [List.length_reverse,address.size])]
    rfl
  ((executed.1.1.get hSome,.frames (traceDepth+2)::.arrayAllocation 16::(reversed.1.2++executed.1.2)),
    executed.2.work+reversed.2)


theorem readAt_erases {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (traceDepth : ℕ) :
    (readAt data address traceDepth).1 = ((BinaryPRGHeapPackedLifetime.readWithTrace data address).1,
      under traceDepth (BinaryPRGHeapPackedLifetime.readWithTrace data address).2) := by
  simp only [readAt,BinaryPRGHeapPackedLifetime.readWithTrace,BinaryPRGHeapPackedLifetime.reverseAddress,
    lookupAt_erases,BinarySeedCursorMeasured.reverseAt_erases,under_append,under_compose,List.append_assoc]
  rfl

def read {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) : (SignedWord × Trace) × ℕ :=
  readAt data address 0

theorem read_erases {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) :
    (read data address).1 = BinaryPRGHeapPackedLifetime.readWithTrace data address := by
  rw [read,readAt_erases,under_zero]

theorem read_data {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) :
    (read data address).1.1 = (data.readWithWork address).1 := by
  rw [read_erases]
  exact BinaryPRGHeapPackedLifetime.readWithTrace_erasure data address

theorem readAt_work {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (traceDepth : ℕ) :
    (readAt data address traceDepth).2 = (data.readWithWork address).2.work := by
  simp only [readAt,Packed.readWithWork,lookupAt_charge,BinarySeedCursorMeasured.reverseAt_work,
    BinaryMidpointTapeLifetime.reverse_work,BinarySeedCursorMeasured.reverseAt_erases,
    BinarySeedPreparationSpace.reverseWithTrace_result,List.reverseAux_eq,List.append_nil,Charge.add]

theorem read_work {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) :
    (read data address).2 = (data.readWithWork address).2.work := readAt_work data address 0

theorem read_bound {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) :
    (read data address).2 ≤ BinaryPRGHeapStoredTree.readBound data.heap.tape.length depth := by
  rw [read_work]
  exact data.readWithWork_bounds address

theorem lookupAt_trace_work (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) (traceDepth : ℕ) :
    (lookupAt tape pointer ruler address traceDepth).1.2.length ≤
      2*((lookupAt tape pointer ruler address traceDepth).2.work+1) := by
  induction ruler generalizing pointer address traceDepth with
  | nil =>
      have hr := BinaryHeapReadMeasured.readAt_trace_work tape pointer (traceDepth+1)
      simp only [lookupAt,Charge.add,List.length_cons]
      omega
  | cons bit ruler ih =>
      have hr := BinaryHeapReadMeasured.readAt_trace_work tape pointer (traceDepth+1)
      simp only [lookupAt]
      cases hc : (BinaryHeapReadMeasured.readAt tape pointer (traceDepth+1)).1.1 with
      | none => simp only [Charge.add,List.length_cons]; omega
      | some cell => cases cell with
        | leaf word => simp only [Charge.add,List.length_cons]; omega
        | branch left right =>
            have hL := ih left address.tail (traceDepth+1)
            have hR := ih right address.tail (traceDepth+1)
            cases address.headD false <;>
              simp only [Bool.false_eq_true,ite_false,ite_true,Charge.add,List.length_cons,List.length_append] <;> omega

theorem lookupAt_frames (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) (traceDepth : ℕ) :
    framePeak (lookupAt tape pointer ruler address traceDepth).1.2 ≤
      traceDepth+(lookupAt tape pointer ruler address traceDepth).2.work+6 := by
  have h := (BinaryPRGHeapAccessLifetime.lookupWithTrace_bound tape pointer ruler address).2
  have hu := framePeak_under traceDepth (BinaryPRGHeapAccessLifetime.lookupWithTrace tape pointer ruler address).2
  rw [lookupAt_erases,lookupAt_charge]
  dsimp only
  omega

theorem readAt_trace_work {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (traceDepth : ℕ) :
    (readAt data address traceDepth).1.2.length ≤ 2*((readAt data address traceDepth).2+2) := by
  have hr := BinarySeedTraceBounds.reverse_trace_work address.bits [] (traceDepth+1)
  have hl := lookupAt_trace_work data.heap.tape data.root data.ruler
    (BinarySeedCursorMeasured.reverseAt address.bits [] (traceDepth+1)).1.1 (traceDepth+1)
  simp only [readAt,List.length_cons,List.length_append]
  omega

theorem readAt_frames {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (traceDepth : ℕ) :
    framePeak (readAt data address traceDepth).1.2 ≤ traceDepth+(readAt data address traceDepth).2+depth+12 := by
  have h := (BinaryPRGHeapPackedLifetime.readWithTrace_bound data address).2
  have hu := framePeak_under traceDepth (BinaryPRGHeapPackedLifetime.readWithTrace data address).2
  rw [readAt_erases,readAt_work]
  dsimp only
  omega

end Blotto.BinaryHeapPackedReadMeasured
