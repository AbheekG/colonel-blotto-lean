import Blotto.NativeArrayBuildControl
import Blotto.BinaryWordStoreLifetime
import Blotto.BinaryPRGHeapTraceUsage

/-! One concrete Boolean index stream for the actual native builder's
callback order. Carries, not natural decoding/subtraction, produce the words.
Each callback index is retained once; old counter versions may share tails.
Payload callbacks/array accesses/reference-bit transport are separate. -/
namespace Blotto.BooleanArrayIndexEnumeration
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def loopWithTrace {α : Type*} : List α → List Bool → (List (List Bool) × List Bool) × Trace
  | [], counter => (([],counter),wrap 8 1 [])
  | _::rest, counter =>
      let advanced := BinaryWordStoreLifetime.carryWithTrace counter
      let next := loopWithTrace rest advanced.1
      ((counter::next.1.1,next.1.2),wrapList 1 16 2 [advanced.2,next.2])

theorem loop_values {α : Type*} (ruler : List α) (counter : List Bool) :
    ((loopWithTrace ruler counter).1.1.map BinaryCarryCounter.value) = List.range' (BinaryCarryCounter.value counter) ruler.length := by
  induction ruler generalizing counter with
  | nil => simp [loopWithTrace]
  | cons item rest ih =>
      simp only [loopWithTrace,List.map_cons,ih,BinaryWordStoreLifetime.carryWithTrace_erases,
        BinaryCarryCounter.value_increment,List.length_cons,List.range'_succ]

theorem loop_final {α : Type*} (ruler : List α) (counter : List Bool) :
    (loopWithTrace ruler counter).1.2 = BinaryCarryCounter.count ruler counter := by
  induction ruler generalizing counter with
  | nil => rfl
  | cons item rest ih => simp only [loopWithTrace,ih,BinaryCarryCounter.count,BinaryWordStoreLifetime.carryWithTrace_erases]

theorem loop_length {α : Type*} (ruler : List α) (counter : List Bool) : (loopWithTrace ruler counter).1.1.length = ruler.length := by
  have h := congrArg List.length (loop_values ruler counter)
  simpa only [List.length_map,List.length_range'] using h

theorem loop_words {α : Type*} (ruler : List α) (counter : List Bool) (hCanonical : BinaryCarryCounter.Canonical counter) :
    ∀ word ∈ (loopWithTrace ruler counter).1.1,BinaryCarryCounter.Canonical word ∧
      BinaryCarryCounter.value word < BinaryCarryCounter.value counter+ruler.length := by
  induction ruler generalizing counter with
  | nil => simp [loopWithTrace]
  | cons item rest ih =>
      intro word hWord
      simp only [loopWithTrace,List.mem_cons] at hWord
      rcases hWord with hWord|hWord
      · subst word
        exact ⟨hCanonical,by simp only [List.length_cons]; omega⟩
      · have hNext : BinaryCarryCounter.Canonical (BinaryWordStoreLifetime.carryWithTrace counter).1 := by
          rw [BinaryWordStoreLifetime.carryWithTrace_erases]
          exact BinaryCarryCounter.increment_canonical counter hCanonical
        have h := ih (BinaryWordStoreLifetime.carryWithTrace counter).1 hNext word hWord
        rw [BinaryWordStoreLifetime.carryWithTrace_erases,BinaryCarryCounter.value_increment] at h
        exact ⟨h.1,by simp only [List.length_cons]; omega⟩

theorem loop_cells {α : Type*} (ruler : List α) (counter : List Bool) :
    BinaryPRGHeapPrimitiveLifetime.cells (loopWithTrace ruler counter).2 =
      17*ruler.length+5*BinaryCarryCounter.countCarryCells ruler counter+8 := by
  induction ruler generalizing counter with
  | nil => simp [loopWithTrace,wrap,combine,BinaryPRGHeapPrimitiveLifetime.cells,listCells,arraySlots,BinaryCarryCounter.countCarryCells]
  | cons item rest ih =>
      have hCarry := (BinaryWordStoreLifetime.carryWithTrace_bounds counter).1
      have hNext := ih (BinaryWordStoreLifetime.carryWithTrace counter).1
      simp only [loopWithTrace,wrapList,wrap,combine,BinaryPRGHeapPrimitiveLifetime.cells,listCells,arraySlots,
        listCells_append,arraySlots_append,listCells_under,arraySlots_under,
        BinaryWordStoreLifetime.carryWithTrace_erases,List.length_cons,BinaryCarryCounter.countCarryCells]
      rw [BinaryWordStoreLifetime.carryWithTrace_erases] at hNext
      unfold BinaryPRGHeapPrimitiveLifetime.cells at hNext
      omega

theorem loop_frames {α : Type*} (ruler : List α) (counter : List Bool) :
    framePeak (loopWithTrace ruler counter).2 ≤ 3*ruler.length+counter.length+4 := by
  induction ruler generalizing counter with
  | nil => simp [loopWithTrace,wrap,combine,framePeak]
  | cons item rest ih =>
      have hCarry := (BinaryWordStoreLifetime.carryWithTrace_bounds counter).2
      have hNext := ih (BinaryWordStoreLifetime.carryWithTrace counter).1
      have hLength : (BinaryWordStoreLifetime.carryWithTrace counter).1.length ≤ counter.length+1 := by
        rw [BinaryWordStoreLifetime.carryWithTrace_erases]
        exact BinaryWordStoreLifetime.carry_length counter
      have hUnderCarry := framePeak_under 2 (BinaryWordStoreLifetime.carryWithTrace counter).2
      have hUnderNext := framePeak_under 2 (loopWithTrace rest (BinaryWordStoreLifetime.carryWithTrace counter).1).2
      simp only [loopWithTrace,wrapList,wrap,combine,framePeak_append,framePeak,List.length_cons]
      omega

theorem loop_usage {α : Type*} (ruler : List α) (counter : List Bool) :
    usage (loopWithTrace ruler counter).2 ≤ 32*ruler.length+8*counter.length+16 := by
  have hOnes : BinaryCarryCounter.ones counter ≤ counter.length := by
    induction counter with
    | nil => rfl
    | cons bit rest ih => cases bit <;> simp only [BinaryCarryCounter.ones,List.length_cons] <;> omega
  have hCells := loop_cells ruler counter
  have hFrames := loop_frames ruler counter
  have hCarry := BinaryCarryCounter.countCarryCells_bound ruler counter
  unfold usage
  omega

def enumerateWithTrace {α : Type*} (ruler : List α) : List (List Bool) × Trace :=
  let result := loopWithTrace ruler []
  (result.1.1,result.2)

theorem enumerate_values {α : Type*} (ruler : List α) :
    ((enumerateWithTrace ruler).1.map BinaryCarryCounter.value) = List.range ruler.length := by
  simpa only [enumerateWithTrace,BinaryCarryCounter.value,BinaryBigEndian.littleValue,List.range_eq_range'] using loop_values ruler []

theorem enumerate_width {α : Type*} (ruler : List α) :
    ∀ word ∈ (enumerateWithTrace ruler).1,word.length ≤ binaryWordWidth ruler.length := by
  intro word hWord
  have h := loop_words ruler [] trivial word hWord
  have hWidth := BinaryCarryCounter.canonical_length_bound word h.1
  exact hWidth.trans (binaryWordWidth_mono (by
    simpa only [BinaryCarryCounter.value,BinaryBigEndian.littleValue,Nat.zero_add] using h.2.le))

theorem enumerate_usage {α : Type*} (ruler : List α) : usage (enumerateWithTrace ruler).2 ≤ 32*ruler.length+16 := by
  simpa only [enumerateWithTrace,List.length_nil,mul_zero,Nat.add_zero] using loop_usage ruler []

theorem native_builder_indices {α β : Type*} {n : ℕ} (ruler : List α) (hLength : ruler.length = n) (produce : Fin n → β) :
    ((enumerateWithTrace ruler).1.map BinaryCarryCounter.value) =
      (NativeArrayCoreControl.build produce).2.filterMap NativeArrayCoreControl.Snapshot.callback := by
  rw [enumerate_values,hLength,NativeArrayCoreControl.build_callbacks]

theorem all_prefix {α : Type*} (ruler : List α) (borrowed steps : ℕ) :
    retainedHeap borrowed (enumerateWithTrace ruler).2 steps ≤ borrowed+32*ruler.length+16 ∧
      framePeak ((enumerateWithTrace ruler).2.take steps) ≤ 32*ruler.length+16 := by
  simpa only [Nat.add_assoc] using BinaryPRGHeapTraceUsage.all_prefix _ _ (enumerate_usage ruler) borrowed steps

end Blotto.BooleanArrayIndexEnumeration
