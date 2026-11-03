import Blotto.BinaryPRGHeapAllocationLifetime

/-! Physical lookup and persistent patch traces include every reached tape
scan, decoded pointer, copied old tape and source call frame. All regions
remain retained; there is no ownership/uniqueness or GC hypothesis. -/

namespace Blotto.BinaryPRGHeapAccessLifetime
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGHeapPrimitiveLifetime BinaryPRGHeapAllocationLifetime
set_option maxHeartbeats 1500000

def lookupWithTrace : List Bool → Pointer → List Bool → List Bool → Option SignedWord × Trace
  | tape,pointer,[],_ =>
      let found := readWithTrace tape pointer
      (match found.1 with | some (.leaf word) => some word | _ => none,
        [.frames 2,.arrayAllocation 8] ++ under 1 found.2)
  | tape,pointer,_ :: ruler,address =>
      let found := readWithTrace tape pointer
      match found.1 with
      | some (.branch left right) =>
          let later := if address.headD false then lookupWithTrace tape right ruler address.tail
            else lookupWithTrace tape left ruler address.tail
          (later.1,[.frames 2,.arrayAllocation 8] ++ under 1 found.2 ++ under 1 later.2)
      | _ => (none,[.frames 2,.arrayAllocation 8] ++ under 1 found.2)

theorem lookupWithTrace_erasure (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) :
    (lookupWithTrace tape pointer ruler address).1 =
      (BinaryPRGWordStoreHeapMachine.lookupWithWork tape pointer ruler address).1 := by
  induction ruler generalizing pointer address with
  | nil =>
      simp only [lookupWithTrace,BinaryPRGWordStoreHeapMachine.lookupWithWork,readWithTrace_erasure]
      rfl
  | cons bit ruler ih =>
      simp only [lookupWithTrace,BinaryPRGWordStoreHeapMachine.lookupWithWork,readWithTrace_erasure]
      cases hc : (BinaryPRGWordStoreHeapMachine.readWithWork tape pointer).1 with
      | none => rfl
      | some cell =>
          cases cell with
          | leaf word => rfl
          | branch left right =>
              by_cases hb : address.headD false = true <;>
                simp only [hb,Bool.false_eq_true,ite_true,ite_false,ih]

theorem lookupWithTrace_bound (tape : List Bool) (pointer : Pointer) (ruler address : List Bool) :
    cells (lookupWithTrace tape pointer ruler address).2 + 8 ≤
        price (BinaryPRGWordStoreHeapMachine.lookupWithWork tape pointer ruler address).2 ∧
      framePeak (lookupWithTrace tape pointer ruler address).2 ≤
        (BinaryPRGWordStoreHeapMachine.lookupWithWork tape pointer ruler address).2.work + 6 := by
  induction ruler generalizing pointer address with
  | nil =>
      have hr := readWithTrace_bound tape pointer
      have hf := framePeak_under 1 (readWithTrace tape pointer).2
      simp only [lookupWithTrace,BinaryPRGWordStoreHeapMachine.lookupWithWork,
        BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,listCells_under,
        arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hr ⊢
      exact ⟨by omega,by omega⟩
  | cons bit ruler ih =>
      have hr := readWithTrace_bound tape pointer
      have hf := framePeak_under 1 (readWithTrace tape pointer).2
      simp only [lookupWithTrace,BinaryPRGWordStoreHeapMachine.lookupWithWork,readWithTrace_erasure]
      cases hc : (BinaryPRGWordStoreHeapMachine.readWithWork tape pointer).1 with
      | none =>
          simp only [BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
            listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hr ⊢
          exact ⟨by omega,by omega⟩
      | some cell =>
          cases cell with
          | leaf word =>
              simp only [BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
                listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hr ⊢
              exact ⟨by omega,by omega⟩
          | branch left right =>
              have hL := ih left address.tail
              have hR := ih right address.tail
              have fL := framePeak_under 1 (lookupWithTrace tape left ruler address.tail).2
              have fR := framePeak_under 1 (lookupWithTrace tape right ruler address.tail).2
              by_cases hb : address.headD false = true <;>
                simp only [hb,Bool.false_eq_true,ite_true,ite_false,BinaryPRGWordStoreHeapMachine.Charge.add,
                  cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,
                  framePeak_append,framePeak,price] at hr hL hR ⊢ <;> exact ⟨by omega,by omega⟩

def patchWithTrace : Heap → Pointer → List Bool → List Bool → SignedWord → Option (Pointer × Heap) × Trace
  | heap,pointer,[],_,word =>
      let found := readWithTrace heap.tape pointer
      match found.1 with
      | some (.leaf _) =>
          let produced := allocateWithTrace heap (.leaf word)
          (some produced.1,[.frames 2,.arrayAllocation 8] ++ under 1 found.2 ++ under 1 produced.2)
      | _ => (none,[.frames 2,.arrayAllocation 8] ++ under 1 found.2)
  | heap,pointer,_ :: ruler,address,word =>
      let found := readWithTrace heap.tape pointer
      match found.1 with
      | some (.branch left right) =>
          let changed := if address.headD false then patchWithTrace heap right ruler address.tail word
            else patchWithTrace heap left ruler address.tail word
          match changed.1 with
          | none => (none,[.frames 2,.arrayAllocation 8] ++ under 1 found.2 ++ under 1 changed.2)
          | some later =>
              let cell := if address.headD false then Cell.branch left later.1 else Cell.branch later.1 right
              let produced := allocateWithTrace later.2 cell
              (some produced.1,[.frames 2,.arrayAllocation 16] ++ under 1 found.2 ++ under 1 changed.2 ++ under 1 produced.2)
      | _ => (none,[.frames 2,.arrayAllocation 8] ++ under 1 found.2)

theorem patchWithTrace_erasure (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) :
    (patchWithTrace heap pointer ruler address word).1 =
      (BinaryPRGWordStoreHeapMachine.patchWithWork heap pointer ruler address word).1 := by
  induction ruler generalizing heap pointer address with
  | nil =>
      simp only [patchWithTrace,BinaryPRGWordStoreHeapMachine.patchWithWork,readWithTrace_erasure]
      cases hc : (BinaryPRGWordStoreHeapMachine.readWithWork heap.tape pointer).1 with
      | none => rfl
      | some cell => cases cell <;> simp only [allocateWithTrace_erasure]
  | cons bit ruler ih =>
      simp only [patchWithTrace,BinaryPRGWordStoreHeapMachine.patchWithWork,readWithTrace_erasure]
      cases hc : (BinaryPRGWordStoreHeapMachine.readWithWork heap.tape pointer).1 with
      | none => rfl
      | some cell =>
          cases cell with
          | leaf old => rfl
          | branch left right =>
              by_cases hb : address.headD false = true <;>
                simp only [hb,Bool.false_eq_true,ite_true,ite_false,ih]
              all_goals
                split <;> rename_i hChanged <;> simp only [hChanged,allocateWithTrace_erasure]

theorem patchWithTrace_bound (heap : Heap) (pointer : Pointer) (ruler address : List Bool) (word : SignedWord) :
    cells (patchWithTrace heap pointer ruler address word).2 + 8 ≤
        price (BinaryPRGWordStoreHeapMachine.patchWithWork heap pointer ruler address word).2 ∧
      framePeak (patchWithTrace heap pointer ruler address word).2 ≤
        (BinaryPRGWordStoreHeapMachine.patchWithWork heap pointer ruler address word).2.work + 8 := by
  induction ruler generalizing heap pointer address with
  | nil =>
      have hr := readWithTrace_bound heap.tape pointer
      have fr := framePeak_under 1 (readWithTrace heap.tape pointer).2
      simp only [patchWithTrace,BinaryPRGWordStoreHeapMachine.patchWithWork,readWithTrace_erasure]
      cases hc : (BinaryPRGWordStoreHeapMachine.readWithWork heap.tape pointer).1 with
      | none =>
          simp only [BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
            listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hr ⊢
          exact ⟨by omega,by omega⟩
      | some cell =>
          cases cell with
          | leaf old =>
              have ha := allocateWithTrace_bound heap (.leaf word)
              have fa := framePeak_under 1 (allocateWithTrace heap (.leaf word)).2
              simp only [BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
                listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hr ha ⊢
              exact ⟨by omega,by omega⟩
          | branch left right =>
              simp only [BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
                listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hr ⊢
              exact ⟨by omega,by omega⟩
  | cons bit ruler ih =>
      have hr := readWithTrace_bound heap.tape pointer
      have fr := framePeak_under 1 (readWithTrace heap.tape pointer).2
      simp only [patchWithTrace,BinaryPRGWordStoreHeapMachine.patchWithWork,readWithTrace_erasure]
      cases hc : (BinaryPRGWordStoreHeapMachine.readWithWork heap.tape pointer).1 with
      | none =>
          simp only [BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
            listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hr ⊢
          exact ⟨by omega,by omega⟩
      | some cell =>
          cases cell with
          | leaf old =>
              simp only [BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
                listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hr ⊢
              exact ⟨by omega,by omega⟩
          | branch left right =>
              have hChild := ih heap (if address.headD false then right else left) address.tail
              have fChild := framePeak_under 1
                (patchWithTrace heap (if address.headD false then right else left) ruler address.tail word).2
              by_cases hb : address.headD false = true
              all_goals
                simp only [hb,Bool.false_eq_true,ite_true,ite_false] at hChild fChild ⊢
                simp only [patchWithTrace_erasure]
                split
                · rename_i hChanged
                  simp only [hChanged]
                  simp only [BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
                    listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hr hChild ⊢
                  exact ⟨by omega,by omega⟩
                · rename_i later hChanged
                  simp only [hChanged]
                  have hAlloc := allocateWithTrace_bound later.2
                    (if address.headD false then .branch left later.1 else .branch later.1 right)
                  have fAlloc := framePeak_under 1 (allocateWithTrace later.2
                    (if address.headD false then .branch left later.1 else .branch later.1 right)).2
                  simp only [hb,Bool.false_eq_true,ite_true,ite_false] at hAlloc fAlloc
                  simp only [BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,
                    listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price] at hr hChild hAlloc ⊢
                  exact ⟨by omega,by omega⟩

theorem lookup_all_prefix {depth : ℕ} {tape : List Bool} {pointer : Pointer}
    {tree : BinaryPRGWordControllerWordStore.Tree depth} (hTree : Realizes tape pointer tree)
    (ruler address : List Bool) (hr : ruler.length = depth) (ha : address.length = depth)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (lookupWithTrace tape pointer ruler address).2 steps ≤ borrowed +
        16 * (BinaryPRGWordStoreHeapMachine.lookupBound tape.length depth +
          BinaryPRGWordStoreHeapMachine.lookupAllocation tape.length depth) ∧
      framePeak ((lookupWithTrace tape pointer ruler address).2.take steps) ≤
        BinaryPRGWordStoreHeapMachine.lookupBound tape.length depth + 6 := by
  have hTrace := lookupWithTrace_bound tape pointer ruler address
  have hCharge := BinaryPRGWordStoreHeapMachine.lookupWithWork_bounds hTree ruler address hr ha
  have hCells : listCells (lookupWithTrace tape pointer ruler address).2 +
      arraySlots (lookupWithTrace tape pointer ruler address).2 ≤
      16 * (BinaryPRGWordStoreHeapMachine.lookupBound tape.length depth +
        BinaryPRGWordStoreHeapMachine.lookupAllocation tape.length depth) := by
    simp only [cells,price] at hTrace
    omega
  exact ⟨BinaryBooleanPrimitiveLifetime.prefix_heap _ _ borrowed steps hCells,
    (framePeak_take_le _ _).trans (hTrace.2.trans (Nat.add_le_add_right hCharge.1 6))⟩

theorem patch_all_prefix {depth : ℕ} (tree : BinaryPRGWordControllerWordStore.Tree depth)
    (heap : Heap) (pointer : Pointer) (hHeap : Valid heap) (hTree : Realizes heap.tape pointer tree)
    (ruler address : List Bool) (hr : ruler.length = depth) (ha : address.length = depth)
    (word : SignedWord) (result : Pointer × Heap)
    (hSuccess : patch heap pointer ruler address word = some result)
    (B : ℕ) (hB : result.2.tape.length ≤ B) (borrowed steps : ℕ) :
    retainedHeap borrowed (patchWithTrace heap pointer ruler address word).2 steps ≤
        borrowed + 32 * BinaryPRGWordStoreHeapMachine.patchBound B depth ∧
      framePeak ((patchWithTrace heap pointer ruler address word).2.take steps) ≤
        BinaryPRGWordStoreHeapMachine.patchBound B depth + 8 := by
  have hTrace := patchWithTrace_bound heap pointer ruler address word
  have hCharge := BinaryPRGWordStoreHeapMachine.patchWithWork_bounds tree heap pointer hHeap hTree
    ruler address hr ha word result hSuccess B hB
  have hCells : listCells (patchWithTrace heap pointer ruler address word).2 +
      arraySlots (patchWithTrace heap pointer ruler address word).2 ≤
      32 * BinaryPRGWordStoreHeapMachine.patchBound B depth := by
    simp only [cells,price] at hTrace
    omega
  exact ⟨BinaryBooleanPrimitiveLifetime.prefix_heap _ _ borrowed steps hCells,
    (framePeak_take_le _ _).trans (hTrace.2.trans (Nat.add_le_add_right hCharge.1 8))⟩

end Blotto.BinaryPRGHeapAccessLifetime
