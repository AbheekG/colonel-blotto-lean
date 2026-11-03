import Blotto.BinaryHeapReadMeasured
import Blotto.BinaryHeapAllocationMeasured
import Blotto.BinaryPRGHeapWriteLifetime
import Blotto.BinarySeedCursorMeasured

/-! Actual persistent patches, writes and write sequences build one trace plan;
only the outer requested entry emits it and forwards the emission charge.
The preceding data/trace/charge and address-reversal ledger remain exact.
Successful path depth covers reversals. Native scalar/reference/allocator/GC
pricing and complete model joins remain separate. -/
namespace Blotto.BinaryHeapWriteMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryTraceDepth
open BinaryTracePlanMeasured (Plan)
open BinaryPRGWordStoreHeapMachine (Charge)
open BinaryPRGHeapPackedStore (Packed)
set_option autoImplicit false
set_option maxHeartbeats 1000000

def patchPlanAt : Heap → Pointer → List Bool → List Bool → SignedWord → ℕ →
    (Option (Pointer × Heap) × Plan) × Charge
  | heap,pointer,[],_,word,traceDepth =>
      let found := BinaryHeapReadMeasured.readAt heap.tape pointer (traceDepth+1)
      match found.1.1 with
      | some (.leaf _) =>
          let produced := BinaryHeapAllocationMeasured.allocateAt heap (.leaf word) (traceDepth+1)
          ((some produced.1.1,.join (.block [.frames (traceDepth+2),.arrayAllocation 8])
            (.join (.block found.1.2) (.block produced.1.2))),found.2.add (produced.2.add ⟨4,4⟩))
      | _ => ((none,.join (.block [.frames (traceDepth+2),.arrayAllocation 8]) (.block found.1.2)),found.2.add ⟨2,4⟩)
  | heap,pointer,_::ruler,address,word,traceDepth =>
      let found := BinaryHeapReadMeasured.readAt heap.tape pointer (traceDepth+1)
      match found.1.1 with
      | some (.branch left right) =>
          let changed := if address.headD false then patchPlanAt heap right ruler address.tail word (traceDepth+1)
            else patchPlanAt heap left ruler address.tail word (traceDepth+1)
          match changed.1.1 with
          | none => ((none,.join (.block [.frames (traceDepth+2),.arrayAllocation 8])
              (.join (.block found.1.2) changed.1.2)),found.2.add (changed.2.add ⟨2,4⟩))
          | some later =>
              let cell := if address.headD false then Cell.branch left later.1 else Cell.branch later.1 right
              let produced := BinaryHeapAllocationMeasured.allocateAt later.2 cell (traceDepth+1)
              ((some produced.1.1,.join (.block [.frames (traceDepth+2),.arrayAllocation 16])
                (.join (.block found.1.2) (.join changed.1.2 (.block produced.1.2)))),
                found.2.add (changed.2.add (produced.2.add ⟨4,4⟩)))
      | _ => ((none,.join (.block [.frames (traceDepth+2),.arrayAllocation 8]) (.block found.1.2)),found.2.add ⟨2,4⟩)

theorem patchPlanAt_data (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) (traceDepth : ℕ) :
    (patchPlanAt heap pointer ruler address word traceDepth).1.1 =
      (BinaryPRGHeapAccessLifetime.patchWithTrace heap pointer ruler address word).1 := by
  induction ruler generalizing heap pointer address traceDepth with
  | nil =>
      simp only [patchPlanAt,BinaryPRGHeapAccessLifetime.patchWithTrace,BinaryHeapReadMeasured.readAt_erases]
      cases (BinaryPRGHeapAllocationLifetime.readWithTrace heap.tape pointer).1 with
      | none => rfl
      | some cell => cases cell <;> simp only [BinaryHeapAllocationMeasured.allocateAt_erases]
  | cons bit ruler ih =>
      simp only [patchPlanAt,BinaryPRGHeapAccessLifetime.patchWithTrace,BinaryHeapReadMeasured.readAt_erases]
      cases (BinaryPRGHeapAllocationLifetime.readWithTrace heap.tape pointer).1 with
      | none => rfl
      | some cell => cases cell with
        | leaf old => rfl
        | branch left right =>
            cases address.headD false <;> simp only [Bool.false_eq_true,ite_false,ite_true,ih]
            all_goals split <;> rename_i hChanged <;> simp only [hChanged,BinaryHeapAllocationMeasured.allocateAt_erases]

theorem patchPlanAt_trace (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) (traceDepth : ℕ) :
    BinaryTracePlanMeasured.denote (patchPlanAt heap pointer ruler address word traceDepth).1.2 =
      under traceDepth (BinaryPRGHeapAccessLifetime.patchWithTrace heap pointer ruler address word).2 := by
  induction ruler generalizing heap pointer address traceDepth with
  | nil =>
      simp only [patchPlanAt,BinaryPRGHeapAccessLifetime.patchWithTrace,BinaryHeapReadMeasured.readAt_erases]
      cases (BinaryPRGHeapAllocationLifetime.readWithTrace heap.tape pointer).1 with
      | none => simp only [BinaryTracePlanMeasured.denote,under_append,under_compose]; rfl
      | some cell => cases cell <;>
          simp only [BinaryTracePlanMeasured.denote,BinaryHeapAllocationMeasured.allocateAt_erases,
            under_append,under_compose,List.append_assoc] <;> rfl
  | cons bit ruler ih =>
      simp only [patchPlanAt,BinaryPRGHeapAccessLifetime.patchWithTrace,BinaryHeapReadMeasured.readAt_erases]
      cases (BinaryPRGHeapAllocationLifetime.readWithTrace heap.tape pointer).1 with
      | none => simp only [BinaryTracePlanMeasured.denote,under_append,under_compose]; rfl
      | some cell => cases cell with
        | leaf old => simp only [BinaryTracePlanMeasured.denote,under_append,under_compose]; rfl
        | branch left right =>
            cases address.headD false <;> simp only [Bool.false_eq_true,ite_false,ite_true,patchPlanAt_data]
            all_goals
              split <;> rename_i hChanged <;>
                simp only [hChanged,BinaryTracePlanMeasured.denote,BinaryHeapAllocationMeasured.allocateAt_erases,
                  ih,under_append,under_compose,List.append_assoc] <;> rfl

theorem patchPlanAt_charge (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) (traceDepth : ℕ) :
    (patchPlanAt heap pointer ruler address word traceDepth).2 =
      (BinaryPRGWordStoreHeapMachine.patchWithWork heap pointer ruler address word).2 := by
  induction ruler generalizing heap pointer address traceDepth with
  | nil =>
      simp only [patchPlanAt,BinaryPRGWordStoreHeapMachine.patchWithWork,BinaryHeapReadMeasured.readAt_erases,
        BinaryPRGHeapAllocationLifetime.readWithTrace_erasure,BinaryHeapReadMeasured.readAt_charge]
      cases (BinaryPRGWordStoreHeapMachine.readWithWork heap.tape pointer).1 with
      | none => rfl
      | some cell => cases cell <;> simp only [BinaryHeapAllocationMeasured.allocateAt_charge]
  | cons bit ruler ih =>
      simp only [patchPlanAt,BinaryPRGWordStoreHeapMachine.patchWithWork,BinaryHeapReadMeasured.readAt_erases,
        BinaryPRGHeapAllocationLifetime.readWithTrace_erasure,BinaryHeapReadMeasured.readAt_charge]
      cases (BinaryPRGWordStoreHeapMachine.readWithWork heap.tape pointer).1 with
      | none => rfl
      | some cell => cases cell with
        | leaf old => rfl
        | branch left right =>
            cases address.headD false <;> simp only [Bool.false_eq_true,ite_false,ite_true,patchPlanAt_data,
              BinaryPRGHeapAccessLifetime.patchWithTrace_erasure,ih]
            all_goals split <;> rename_i hChanged <;> simp only [hChanged,BinaryHeapAllocationMeasured.allocateAt_charge]

def patchAtMeasured (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) (traceDepth : ℕ) :
    ((Option (Pointer × Heap) × Trace) × Charge) × ℕ :=
  let planned := patchPlanAt heap pointer ruler address word traceDepth
  let emitted := BinaryTracePlanMeasured.emit planned.1.2 []
  (((planned.1.1,emitted.1),planned.2),emitted.2)

def patch (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) :
    (Option (Pointer × Heap) × Trace) × Charge := (patchAtMeasured heap pointer ruler address word 0).1

theorem patch_erases (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) :
    (patch heap pointer ruler address word).1 = BinaryPRGHeapAccessLifetime.patchWithTrace heap pointer ruler address word := by
  simp only [patch,patchAtMeasured,BinaryTracePlanMeasured.emit_data,List.append_nil,
    patchPlanAt_data,patchPlanAt_trace,under_zero]

theorem patch_data (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) :
    (patch heap pointer ruler address word).1.1 = (BinaryPRGWordStoreHeapMachine.patchWithWork heap pointer ruler address word).1 := by
  rw [patch_erases]
  exact BinaryPRGHeapAccessLifetime.patchWithTrace_erasure heap pointer ruler address word

theorem patch_charge (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) :
    (patch heap pointer ruler address word).2 = (BinaryPRGWordStoreHeapMachine.patchWithWork heap pointer ruler address word).2 :=
  patchPlanAt_charge heap pointer ruler address word 0

theorem patchPlanAt_work_lower (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord)
    (traceDepth : ℕ) (hSome : (patchPlanAt heap pointer ruler address word traceDepth).1.1.isSome) :
    4*(ruler.length+1) ≤ (patchPlanAt heap pointer ruler address word traceDepth).2.work := by
  induction ruler generalizing heap pointer address traceDepth with
  | nil =>
      simp only [patchPlanAt] at hSome ⊢
      cases hf : (BinaryHeapReadMeasured.readAt heap.tape pointer (traceDepth+1)).1.1 with
      | none => simp [hf] at hSome
      | some cell => cases cell with
        | branch left right => simp [hf] at hSome
        | leaf old => simp only [Charge.add,List.length_nil]; omega
  | cons bit ruler ih =>
      simp only [patchPlanAt] at hSome ⊢
      cases hf : (BinaryHeapReadMeasured.readAt heap.tape pointer (traceDepth+1)).1.1 with
      | none => simp [hf] at hSome
      | some cell => cases cell with
        | leaf old => simp [hf] at hSome
        | branch left right =>
            cases hb : address.headD false <;>
              simp only [hf,hb,Bool.false_eq_true,ite_false,ite_true] at hSome ⊢
            · cases hc : (patchPlanAt heap left ruler address.tail word (traceDepth+1)).1.1 with
              | none => simp [hc] at hSome
              | some result =>
                  have hl := ih heap left address.tail (traceDepth+1) (by rw [hc]; rfl)
                  simp only [Charge.add,List.length_cons]
                  omega
            · cases hc : (patchPlanAt heap right ruler address.tail word (traceDepth+1)).1.1 with
              | none => simp [hc] at hSome
              | some result =>
                  have hl := ih heap right address.tail (traceDepth+1) (by rw [hc]; rfl)
                  simp only [Charge.add,List.length_cons]
                  omega

theorem patch_work_lower (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord)
    (hSome : (patch heap pointer ruler address word).1.1.isSome) :
    4*(ruler.length+1) ≤ (patch heap pointer ruler address word).2.work :=
  patchPlanAt_work_lower heap pointer ruler address word 0 hSome

def writePlanAt {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (traceDepth : ℕ) : (Packed depth × Plan) × (Charge × ℕ) :=
  let reversed := BinarySeedCursorMeasured.reverseAt address.bits [] (traceDepth+1)
  let executed := patchPlanAt data.heap data.root data.ruler reversed.1.1 word (traceDepth+1)
  have hSome : executed.1.1.isSome := by
    rw [patchPlanAt_data,BinaryPRGHeapAccessLifetime.patchWithTrace_erasure,
      BinarySeedCursorMeasured.reverseAt_erases,BinarySeedPreparationSpace.reverseWithTrace_result,
      List.reverseAux_eq,List.append_nil]
    exact data.write_isSome address word
  let result := executed.1.1.get hSome
  have hResult : (BinaryPRGWordStoreHeapMachine.patchWithWork data.heap data.root data.ruler address.bits.reverse word).1 = some result := by
    have h := (Option.some_get hSome).symm
    change executed.1.1 = some result at h
    simpa only [executed,reversed,patchPlanAt_data,BinaryPRGHeapAccessLifetime.patchWithTrace_erasure,
      BinarySeedCursorMeasured.reverseAt_erases,BinarySeedPreparationSpace.reverseWithTrace_result,
      List.reverseAux_eq,List.append_nil] using h
  let h := data.write_result address word result hResult
  ((⟨data.ruler,data.size,result.2,result.1,h.1,h.2⟩,
    .join (.block [.frames (traceDepth+2),.arrayAllocation 16]) (.join (.block reversed.1.2) executed.1.2)),
    (executed.2,reversed.2))

theorem writePlanAt_data {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (traceDepth : ℕ) : (writePlanAt data address word traceDepth).1.1 =
      (BinaryPRGHeapPackedLifetime.writeWithTrace data address word).1 := by
  simp only [writePlanAt,BinaryPRGHeapPackedLifetime.writeWithTrace,BinaryPRGHeapPackedLifetime.reverseAddress,
    patchPlanAt_data,BinarySeedCursorMeasured.reverseAt_erases]

theorem writePlanAt_trace {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (traceDepth : ℕ) : BinaryTracePlanMeasured.denote (writePlanAt data address word traceDepth).1.2 =
      under traceDepth (BinaryPRGHeapPackedLifetime.writeWithTrace data address word).2 := by
  simp only [writePlanAt,BinaryPRGHeapPackedLifetime.writeWithTrace,BinaryPRGHeapPackedLifetime.reverseAddress,
    BinaryTracePlanMeasured.denote,patchPlanAt_trace,BinarySeedCursorMeasured.reverseAt_erases,
    under_append,under_compose,List.append_assoc]
  rfl

theorem writePlanAt_charge {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (traceDepth : ℕ) : (writePlanAt data address word traceDepth).2.1 = (data.writeWithWork address word).2 := by
  simp only [writePlanAt,Packed.writeWithWork,patchPlanAt_charge,BinarySeedCursorMeasured.reverseAt_erases,
    BinarySeedPreparationSpace.reverseWithTrace_result,List.reverseAux_eq,List.append_nil]

theorem writePlanAt_reversal {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (traceDepth : ℕ) : (writePlanAt data address word traceDepth).2.2 = 4*address.bits.length+2 := by
  simp only [writePlanAt,BinarySeedCursorMeasured.reverseAt_work,BinaryMidpointTapeLifetime.reverse_work]

theorem writePlanAt_reversal_le_charge {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (traceDepth : ℕ) : (writePlanAt data address word traceDepth).2.2 ≤ (writePlanAt data address word traceDepth).2.1.work := by
  have hSome : (patchPlanAt data.heap data.root data.ruler address.bits.reverse word (traceDepth+1)).1.1.isSome := by
    rw [patchPlanAt_data,BinaryPRGHeapAccessLifetime.patchWithTrace_erasure]
    exact data.write_isSome address word
  have hLower := patchPlanAt_work_lower data.heap data.root data.ruler address.bits.reverse word (traceDepth+1) hSome
  rw [data.size] at hLower
  rw [writePlanAt_reversal,writePlanAt_charge,address.size]
  simpa only [patchPlanAt_charge,Packed.writeWithWork] using (show 4*depth+2 ≤
    (patchPlanAt data.heap data.root data.ruler address.bits.reverse word (traceDepth+1)).2.work by omega)

def writeAtMeasured {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (traceDepth : ℕ) : ((Packed depth × Trace) × (Charge × ℕ)) × ℕ :=
  let planned := writePlanAt data address word traceDepth
  let emitted := BinaryTracePlanMeasured.emit planned.1.2 []
  (((planned.1.1,emitted.1),planned.2),emitted.2)

def write {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    (Packed depth × Trace) × (Charge × ℕ) := (writeAtMeasured data address word 0).1

theorem write_erases {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    (write data address word).1 = BinaryPRGHeapPackedLifetime.writeWithTrace data address word := by
  simp only [write,writeAtMeasured,BinaryTracePlanMeasured.emit_data,List.append_nil,
    writePlanAt_data,writePlanAt_trace,under_zero]

theorem write_data {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    (write data address word).1.1 = (data.writeWithWork address word).1 := by
  rw [write_erases,BinaryPRGHeapPackedLifetime.writeWithTrace_erasure]

theorem write_charge {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    (write data address word).2.1 = (data.writeWithWork address word).2 := writePlanAt_charge data address word 0

theorem write_reversal {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    (write data address word).2.2 = 4*address.bits.length+2 := writePlanAt_reversal data address word 0

theorem write_reversal_le_charge {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    (write data address word).2.2 ≤ (write data address word).2.1.work := writePlanAt_reversal_le_charge data address word 0

def executePlanAt {depth : ℕ} (data : Packed depth) :
    List (BinaryPRGHeapWriteSequence.Change depth) → ℕ → (Packed depth × Plan) × (Charge × ℕ)
  | [],traceDepth => ((data,.block [.frames (traceDepth+1),.arrayAllocation 8]),(⟨1,0⟩,0))
  | change::rest,traceDepth =>
      let current := writePlanAt data change.1 change.2 (traceDepth+1)
      let later := executePlanAt current.1.1 rest (traceDepth+1)
      ((later.1.1,.join (.block [.frames (traceDepth+2),.arrayAllocation 16]) (.join current.1.2 later.1.2)),
        (⟨current.2.1.work+later.2.1.work+4,current.2.1.allocatedBits+later.2.1.allocatedBits+4⟩,
          current.2.2+later.2.2))

theorem executePlanAt_data {depth : ℕ} (data : Packed depth) (changes : List (BinaryPRGHeapWriteSequence.Change depth))
    (traceDepth : ℕ) : (executePlanAt data changes traceDepth).1.1 =
      (BinaryPRGHeapWriteLifetime.executeWithTrace data changes).1 := by
  induction changes generalizing data traceDepth with
  | nil => rfl
  | cons change rest ih => simp only [executePlanAt,BinaryPRGHeapWriteLifetime.executeWithTrace,writePlanAt_data,ih]

theorem executePlanAt_trace {depth : ℕ} (data : Packed depth) (changes : List (BinaryPRGHeapWriteSequence.Change depth))
    (traceDepth : ℕ) : BinaryTracePlanMeasured.denote (executePlanAt data changes traceDepth).1.2 =
      under traceDepth (BinaryPRGHeapWriteLifetime.executeWithTrace data changes).2 := by
  induction changes generalizing data traceDepth with
  | nil => rfl
  | cons change rest ih =>
      simp only [executePlanAt,BinaryPRGHeapWriteLifetime.executeWithTrace,BinaryTracePlanMeasured.denote,
        writePlanAt_data,writePlanAt_trace,ih,under_append,under_compose,List.append_assoc]
      rfl

theorem executePlanAt_charge {depth : ℕ} (data : Packed depth) (changes : List (BinaryPRGHeapWriteSequence.Change depth))
    (traceDepth : ℕ) : (executePlanAt data changes traceDepth).2.1 =
      (BinaryPRGHeapWriteSequence.executeWithWork data changes).2 := by
  induction changes generalizing data traceDepth with
  | nil => rfl
  | cons change rest ih =>
      simp only [executePlanAt,BinaryPRGHeapWriteSequence.executeWithWork,writePlanAt_charge,writePlanAt_data,
        BinaryPRGHeapPackedLifetime.writeWithTrace_erasure,ih]

theorem executePlanAt_reversals_le_charge {depth : ℕ} (data : Packed depth)
    (changes : List (BinaryPRGHeapWriteSequence.Change depth)) (traceDepth : ℕ) :
    (executePlanAt data changes traceDepth).2.2 ≤ (executePlanAt data changes traceDepth).2.1.work := by
  induction changes generalizing data traceDepth with
  | nil => simp [executePlanAt]
  | cons change rest ih =>
      have hCurrent := writePlanAt_reversal_le_charge data change.1 change.2 (traceDepth+1)
      have hLater := ih (writePlanAt data change.1 change.2 (traceDepth+1)).1.1 (traceDepth+1)
      simp only [executePlanAt]
      omega

theorem executePlanAt_reversals {depth : ℕ} (data : Packed depth)
    (changes : List (BinaryPRGHeapWriteSequence.Change depth)) (traceDepth : ℕ) :
    (executePlanAt data changes traceDepth).2.2 = changes.length*(4*depth+2) := by
  induction changes generalizing data traceDepth with
  | nil => simp [executePlanAt]
  | cons change rest ih =>
      have hSize : change.1.bits.length = depth := change.1.size
      simp only [executePlanAt,writePlanAt_reversal,ih,List.length_cons,hSize,Nat.add_mul,Nat.one_mul]
      omega

def executeAtMeasured {depth : ℕ} (data : Packed depth) (changes : List (BinaryPRGHeapWriteSequence.Change depth))
    (traceDepth : ℕ) : ((Packed depth × Trace) × (Charge × ℕ)) × ℕ :=
  let planned := executePlanAt data changes traceDepth
  let emitted := BinaryTracePlanMeasured.emit planned.1.2 []
  (((planned.1.1,emitted.1),planned.2),emitted.2)

def execute {depth : ℕ} (data : Packed depth) (changes : List (BinaryPRGHeapWriteSequence.Change depth)) :
    (Packed depth × Trace) × (Charge × ℕ) := (executeAtMeasured data changes 0).1

theorem execute_erases {depth : ℕ} (data : Packed depth) (changes : List (BinaryPRGHeapWriteSequence.Change depth)) :
    (execute data changes).1 = BinaryPRGHeapWriteLifetime.executeWithTrace data changes := by
  simp only [execute,executeAtMeasured,BinaryTracePlanMeasured.emit_data,List.append_nil,
    executePlanAt_data,executePlanAt_trace,under_zero]

theorem execute_data {depth : ℕ} (data : Packed depth) (changes : List (BinaryPRGHeapWriteSequence.Change depth)) :
    (execute data changes).1.1 = (BinaryPRGHeapWriteSequence.executeWithWork data changes).1 := by
  rw [execute_erases,BinaryPRGHeapWriteLifetime.executeWithTrace_erasure]

theorem execute_charge {depth : ℕ} (data : Packed depth) (changes : List (BinaryPRGHeapWriteSequence.Change depth)) :
    (execute data changes).2.1 = (BinaryPRGHeapWriteSequence.executeWithWork data changes).2 := executePlanAt_charge data changes 0

theorem execute_reversals_le_charge {depth : ℕ} (data : Packed depth) (changes : List (BinaryPRGHeapWriteSequence.Change depth)) :
    (execute data changes).2.2 ≤ (execute data changes).2.1.work := executePlanAt_reversals_le_charge data changes 0

theorem write_with_reversal_bound {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    (write data address word).2.1.work+(write data address word).2.2 ≤ 2*(data.writeWithWork address word).2.work := by
  have h := write_reversal_le_charge data address word
  rw [← write_charge]
  omega

theorem execute_with_reversals_bound {depth : ℕ} (data : Packed depth) (changes : List (BinaryPRGHeapWriteSequence.Change depth)) :
    (execute data changes).2.1.work+(execute data changes).2.2 ≤
      2*(BinaryPRGHeapWriteSequence.executeWithWork data changes).2.work := by
  have h := execute_reversals_le_charge data changes
  rw [← execute_charge]
  omega


theorem patchPlanAt_budget (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) (traceDepth : ℕ) :
    BinaryTracePlanMeasured.payload (patchPlanAt heap pointer ruler address word traceDepth).1.2+
      BinaryTracePlanMeasured.nodes (patchPlanAt heap pointer ruler address word traceDepth).1.2 ≤
        4*(patchPlanAt heap pointer ruler address word traceDepth).2.work := by
  induction ruler generalizing heap pointer address traceDepth with
  | nil =>
      have hr := BinaryHeapReadMeasured.readAt_trace_work heap.tape pointer (traceDepth+1)
      simp only [patchPlanAt]
      cases hf : (BinaryHeapReadMeasured.readAt heap.tape pointer (traceDepth+1)).1.1 with
      | none =>
          simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,Charge.add,List.length_cons,List.length_nil]
          omega
      | some cell => cases cell with
        | branch left right =>
            simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,Charge.add,List.length_cons,List.length_nil]
            omega
        | leaf old =>
            have ha := BinaryHeapAllocationMeasured.allocateAt_trace_work heap (.leaf word) (traceDepth+1)
            simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,Charge.add,List.length_cons,List.length_nil]
            omega
  | cons bit ruler ih =>
      have hr := BinaryHeapReadMeasured.readAt_trace_work heap.tape pointer (traceDepth+1)
      simp only [patchPlanAt]
      cases hf : (BinaryHeapReadMeasured.readAt heap.tape pointer (traceDepth+1)).1.1 with
      | none =>
          simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,Charge.add,List.length_cons,List.length_nil]
          omega
      | some cell => cases cell with
        | leaf old =>
            simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,Charge.add,List.length_cons,List.length_nil]
            omega
        | branch left right =>
            cases hb : address.headD false <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true]
            · have hl := ih heap left address.tail (traceDepth+1)
              cases hc : (patchPlanAt heap left ruler address.tail word (traceDepth+1)).1.1 with
              | none =>
                  simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,Charge.add,List.length_cons,List.length_nil]
                  omega
              | some later =>
                  have ha := BinaryHeapAllocationMeasured.allocateAt_trace_work later.2 (.branch later.1 right) (traceDepth+1)
                  simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,Charge.add,List.length_cons,List.length_nil]
                  omega
            · have hl := ih heap right address.tail (traceDepth+1)
              cases hc : (patchPlanAt heap right ruler address.tail word (traceDepth+1)).1.1 with
              | none =>
                  simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,Charge.add,List.length_cons,List.length_nil]
                  omega
              | some later =>
                  have ha := BinaryHeapAllocationMeasured.allocateAt_trace_work later.2 (.branch left later.1) (traceDepth+1)
                  simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,Charge.add,List.length_cons,List.length_nil]
                  omega

theorem writePlanAt_budget {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (traceDepth : ℕ) : BinaryTracePlanMeasured.payload (writePlanAt data address word traceDepth).1.2+
      BinaryTracePlanMeasured.nodes (writePlanAt data address word traceDepth).1.2 ≤
        8*((writePlanAt data address word traceDepth).2.1.work+1) := by
  have hp := patchPlanAt_budget data.heap data.root data.ruler
    (BinarySeedCursorMeasured.reverseAt address.bits [] (traceDepth+1)).1.1 word (traceDepth+1)
  have hr := BinarySeedTraceBounds.reverse_trace_work address.bits [] (traceDepth+1)
  have hv := writePlanAt_reversal_le_charge data address word traceDepth
  simp only [writePlanAt] at hv
  simp only [writePlanAt,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,List.length_cons,List.length_nil]
  omega

theorem executePlanAt_budget {depth : ℕ} (data : Packed depth)
    (changes : List (BinaryPRGHeapWriteSequence.Change depth)) (traceDepth : ℕ) :
    BinaryTracePlanMeasured.payload (executePlanAt data changes traceDepth).1.2+
      BinaryTracePlanMeasured.nodes (executePlanAt data changes traceDepth).1.2 ≤
        8*((executePlanAt data changes traceDepth).2.1.work+1) := by
  induction changes generalizing data traceDepth with
  | nil => simp [executePlanAt,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes]
  | cons change rest ih =>
      have hw := writePlanAt_budget data change.1 change.2 (traceDepth+1)
      have hl := ih (writePlanAt data change.1 change.2 (traceDepth+1)).1.1 (traceDepth+1)
      simp only [executePlanAt,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,List.length_cons,List.length_nil]
      omega

theorem patchAtMeasured_emission (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) (traceDepth : ℕ) :
    (patchAtMeasured heap pointer ruler address word traceDepth).2 ≤
      16*(patchAtMeasured heap pointer ruler address word traceDepth).1.2.work := by
  have h := BinaryTracePlanMeasured.emit_work_bound _ [] _ (patchPlanAt_budget heap pointer ruler address word traceDepth)
  change (BinaryTracePlanMeasured.emit (patchPlanAt heap pointer ruler address word traceDepth).1.2 []).2 ≤
    16*(patchPlanAt heap pointer ruler address word traceDepth).2.work
  omega

theorem writeAtMeasured_emission {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (traceDepth : ℕ) : (writeAtMeasured data address word traceDepth).2 ≤
      32*((writeAtMeasured data address word traceDepth).1.2.1.work+1) := by
  have h := BinaryTracePlanMeasured.emit_work_bound _ [] _ (writePlanAt_budget data address word traceDepth)
  change (BinaryTracePlanMeasured.emit (writePlanAt data address word traceDepth).1.2 []).2 ≤
    32*((writePlanAt data address word traceDepth).2.1.work+1)
  omega

theorem executeAtMeasured_emission {depth : ℕ} (data : Packed depth)
    (changes : List (BinaryPRGHeapWriteSequence.Change depth)) (traceDepth : ℕ) :
    (executeAtMeasured data changes traceDepth).2 ≤ 32*((executeAtMeasured data changes traceDepth).1.2.1.work+1) := by
  have h := BinaryTracePlanMeasured.emit_work_bound _ [] _ (executePlanAt_budget data changes traceDepth)
  change (BinaryTracePlanMeasured.emit (executePlanAt data changes traceDepth).1.2 []).2 ≤
    32*((executePlanAt data changes traceDepth).2.1.work+1)
  omega

theorem executeAtMeasured_source_reversals_emission {depth : ℕ} (data : Packed depth)
    (changes : List (BinaryPRGHeapWriteSequence.Change depth)) (traceDepth : ℕ) :
    (executeAtMeasured data changes traceDepth).1.2.1.work+(executeAtMeasured data changes traceDepth).1.2.2+
      (executeAtMeasured data changes traceDepth).2 ≤ 34*((executeAtMeasured data changes traceDepth).1.2.1.work+1) := by
  have he := executeAtMeasured_emission data changes traceDepth
  have hr := executePlanAt_reversals_le_charge data changes traceDepth
  change (executeAtMeasured data changes traceDepth).1.2.2 ≤ (executeAtMeasured data changes traceDepth).1.2.1.work at hr
  omega

theorem execute_emission_frames {depth : ℕ} (data : Packed depth)
    (changes : List (BinaryPRGHeapWriteSequence.Change depth)) (traceDepth : ℕ) :
    BinaryTracePlanMeasured.emitFrames (executePlanAt data changes traceDepth).1.2 ≤
      8*((executePlanAt data changes traceDepth).2.1.work+1)+1 := by
  have hf := BinaryTracePlanMeasured.emitFrames_bound (executePlanAt data changes traceDepth).1.2
  have hp := executePlanAt_budget data changes traceDepth
  omega

theorem execute_plan_references {depth : ℕ} (data : Packed depth)
    (changes : List (BinaryPRGHeapWriteSequence.Change depth)) (traceDepth : ℕ) :
    BinaryTracePlanMeasured.planReferences (executePlanAt data changes traceDepth).1.2 ≤
      16*((executePlanAt data changes traceDepth).2.1.work+1) := by
  have hr := BinaryTracePlanMeasured.planReferences_bound (executePlanAt data changes traceDepth).1.2
  have hp := executePlanAt_budget data changes traceDepth
  omega

theorem execute_emission_width {depth : ℕ} (data : Packed depth)
    (changes : List (BinaryPRGHeapWriteSequence.Change depth)) (traceDepth : ℕ) :
    binaryWordWidth (executeAtMeasured data changes traceDepth).2 ≤
      binaryWordWidth (32*((BinaryPRGHeapWriteSequence.executeWithWork data changes).2.work+1)) := by
  apply binaryWordWidth_mono
  simpa only [executeAtMeasured,executePlanAt_charge] using executeAtMeasured_emission data changes traceDepth

end Blotto.BinaryHeapWriteMeasured
