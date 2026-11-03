import Blotto.BinaryPRGHeapAccessLifetime
import Blotto.BinaryPRGHeapResourceUpdateBudget

/-! The packed physical resource-store boundary adds the actual reversed
address and result records to tape-access traces. Consecutive writes retain
old, intermediate and final tapes without uniqueness or reclamation. -/

namespace Blotto.BinaryPRGHeapPackedLifetime
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGHeapPrimitiveLifetime BinaryPRGHeapAccessLifetime
open BinaryPRGHeapPackedStore (Packed)
set_option maxHeartbeats 1500000

def reverseAddress (bits : List Bool) : List Bool × Trace := reverseWithTrace bits []

theorem reverseAddress_erasure (bits : List Bool) : (reverseAddress bits).1 = bits.reverse := by
  simp only [reverseAddress,reverseWithTrace_result,List.reverseAux_eq,List.append_nil]

def readWithTrace {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) : SignedWord × Trace :=
  let reversed := reverseAddress address.bits
  let executed := BinaryPRGHeapAccessLifetime.lookupWithTrace data.heap.tape data.root data.ruler reversed.1
  (executed.1.get (by
    rw [lookupWithTrace_erasure,reverseAddress_erasure]
    obtain ⟨tree,hTree⟩ := data.realized
    rw [BinaryPRGWordStoreHeapMachine.lookupWithWork_erasure,
      lookup_realizes hTree data.ruler address.bits.reverse data.size (by rw [List.length_reverse,address.size])]
    rfl),[.frames 2,.arrayAllocation 16] ++ under 1 reversed.2 ++ under 1 executed.2)

theorem readWithTrace_erasure {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) :
    (readWithTrace data address).1 = (data.readWithWork address).1 := by
  simp only [readWithTrace,Packed.readWithWork,lookupWithTrace_erasure,reverseAddress_erasure]

theorem readWithTrace_bound {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) :
    cells (readWithTrace data address).2 + 8 ≤
        price (data.readWithWork address).2 + 2 * depth + 32 ∧
      framePeak (readWithTrace data address).2 ≤ (data.readWithWork address).2.work + depth + 12 := by
  have hAccess := lookupWithTrace_bound data.heap.tape data.root data.ruler address.bits.reverse
  have fAccess := framePeak_under 1
    (BinaryPRGHeapAccessLifetime.lookupWithTrace data.heap.tape data.root data.ruler address.bits.reverse).2
  have hReverse := reverseWithTrace_cells address.bits []
  have aReverse := reverseWithTrace_arrays address.bits []
  have fReverse := (framePeak_under 1 (reverseAddress address.bits).2).trans
    (Nat.add_le_add_left (reverseWithTrace_frames address.bits []) 1)
  simp only [readWithTrace,Packed.readWithWork,reverseAddress,reverseWithTrace_result,List.reverseAux_eq,List.append_nil,
    BinaryPRGWordStoreHeapMachine.Charge.add,cells,listCells_append,arraySlots_append,listCells_under,
    arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,price,address.size] at hAccess hReverse aReverse fReverse ⊢
  exact ⟨by omega,by omega⟩

def writeWithTrace {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    Packed depth × Trace :=
  let reversed := reverseAddress address.bits
  let executed := patchWithTrace data.heap data.root data.ruler reversed.1 word
  have hSome : executed.1.isSome := by
    rw [patchWithTrace_erasure,reverseAddress_erasure]
    exact data.write_isSome address word
  let result := executed.1.get hSome
  have hResult : (BinaryPRGWordStoreHeapMachine.patchWithWork data.heap data.root data.ruler address.bits.reverse word).1 =
      some result := by
    have h := (Option.some_get hSome).symm
    change executed.1 = some result at h
    simpa only [executed,reversed,patchWithTrace_erasure,reverseAddress_erasure] using h
  let h := data.write_result address word result hResult
  (⟨data.ruler,data.size,result.2,result.1,h.1,h.2⟩,
    [.frames 2,.arrayAllocation 16] ++ under 1 reversed.2 ++ under 1 executed.2)

theorem writeWithTrace_erasure {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    (writeWithTrace data address word).1 = (data.writeWithWork address word).1 := by
  simp only [writeWithTrace,Packed.writeWithWork,patchWithTrace_erasure,reverseAddress_erasure]

theorem writeWithTrace_bound {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    cells (writeWithTrace data address word).2 + 8 ≤
        price (data.writeWithWork address word).2 + 2 * depth + 32 ∧
      framePeak (writeWithTrace data address word).2 ≤ (data.writeWithWork address word).2.work + depth + 12 := by
  have hAccess := patchWithTrace_bound data.heap data.root data.ruler address.bits.reverse word
  have fAccess := framePeak_under 1 (patchWithTrace data.heap data.root data.ruler address.bits.reverse word).2
  have hReverse := reverseWithTrace_cells address.bits []
  have aReverse := reverseWithTrace_arrays address.bits []
  have fReverse := (framePeak_under 1 (reverseAddress address.bits).2).trans
    (Nat.add_le_add_left (reverseWithTrace_frames address.bits []) 1)
  simp only [writeWithTrace,Packed.writeWithWork,reverseAddress,reverseWithTrace_result,List.reverseAux_eq,List.append_nil,
    cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,
    framePeak_append,framePeak,price,address.size] at hAccess hReverse aReverse fReverse ⊢
  exact ⟨by omega,by omega⟩

def writeReservation (H depth : ℕ) : ℕ :=
  32 * BinaryPRGWordStoreHeapMachine.patchBound H depth + 2 * depth + 32

theorem writeWithTrace_controlled {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth) (word : SignedWord)
    (P H : ℕ) (hP : 0 < P)
    (hSpace : data.heap.tape.length + (depth + 1 + word.numerator.length + word.denominator.length) * (4 * P + 5) ≤ H)
    (hRoom : H < 2^P) :
    cells (writeWithTrace data address word).2 + 8 ≤ writeReservation H depth ∧
      framePeak (writeWithTrace data address word).2 ≤
        BinaryPRGWordStoreHeapMachine.patchBound H depth + depth + 12 := by
  have hCharge := data.writeWithWork_controlled address word P hP (hSpace.trans_lt hRoom)
  have hMono := BinaryPRGHeapStoredTree.patchBound_mono hSpace depth
  have hTrace := writeWithTrace_bound data address word
  unfold price at hTrace
  unfold writeReservation
  omega

def twoWritesWithTrace {depth : ℕ} (data : Packed depth) (first second : FixedBinaryWord depth)
    (chosen other : SignedWord) : Packed depth × Trace :=
  let intermediate := writeWithTrace data first chosen
  let next := writeWithTrace intermediate.1 second other
  (next.1,[.frames 2,.arrayAllocation 16] ++ under 1 intermediate.2 ++ under 1 next.2)

theorem twoWritesWithTrace_erasure {depth : ℕ} (data : Packed depth) (first second : FixedBinaryWord depth)
    (chosen other : SignedWord) : (twoWritesWithTrace data first second chosen other).1 =
      ((data.writeWithWork first chosen).1.writeWithWork second other).1 := by
  simp only [twoWritesWithTrace,writeWithTrace_erasure]

end Blotto.BinaryPRGHeapPackedLifetime
