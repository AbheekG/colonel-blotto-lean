import Blotto.NativeArrayConversionCore
import Blotto.BooleanArrayIndexEnumeration
import Blotto.BinaryLifetimeListArray

/-! The control inventory applies to the actual native array wrappers.
Operand widths and index streams are derived internally from array/list size.
Full-capacity reference reservations are checked at the source-slot scope;
physical reference bit transport and host capacity/ownership remain separate. -/
namespace Blotto.NativeArrayConversionControl
open NativeArrayConversionCore

theorem pack_source {α : Type*} (items : List α) :
    (pack items).1 = (BinaryLifetimeListArray.toArrayWithTrace items).1 := by
  rw [pack_state,BinaryLifetimeListArray.toArrayWithTrace_state]

theorem seed_pack_source (items : List Bool) :
    (pack items).1 = (BinarySeedPreparationSpace.toArrayWithTrace items).1 := by
  rw [pack_state,BinarySeedPreparationSpace.toArrayWithTrace_result]

theorem build_source {n : ℕ} {α : Type*} (produce : Fin n → α × BinarySeedPreparationSpace.Trace) :
    (NativeArrayCoreControl.build (fun j => (produce j).1)).1 = (BinaryLifetimeArray.build n produce).1.data := by
  rw [NativeArrayCoreControl.build_state,BinaryLifetimeArray.build_erases]
  rfl

theorem pack_scalar_width {α : Type*} (items : List α) :
    ∀ s ∈ (pack items).2,∀ value ∈ s.operands items.length,binaryWordWidth value ≤ binaryWordWidth (items.length+1) := by
  intro s hs value hv
  exact binaryWordWidth_mono ((PushSnapshot.operand_bound (pack_valid items s hs)) value hv)

theorem read_scalar_width {α : Type*} (data : Array α) :
    ∀ s ∈ (read data).2,∀ value ∈ s.operands data.size,binaryWordWidth value ≤ binaryWordWidth (data.size+1) := by
  intro s hs value hv
  exact binaryWordWidth_mono ((ReadSnapshot.operand_bound (read_valid data s hs)) value hv)

theorem read_index_bound {α : Type*} (data : Array α) (s : ReadSnapshot) (hs : s ∈ (read data).2)
    (hRead : s.remaining ≠ 0) : s.index < data.size := by
  have h := read_valid data s hs
  unfold ReadSnapshot.Valid at h
  omega

def PushSnapshot.pushIndex (s : PushSnapshot) : Option ℕ :=
  match s.remaining with
  | 0 => none
  | _+1 => some s.used

theorem pushLoop_indices {α : Type*} (items : List α) (acc : Array α) :
    (pushLoop items acc).2.filterMap PushSnapshot.pushIndex = List.range' acc.size items.length := by
  induction items generalizing acc with
  | nil => simp [pushLoop,PushSnapshot.pushIndex]
  | cons item rest ih => simp only [pushLoop,List.filterMap_cons,PushSnapshot.pushIndex,ih,Array.size_push,
      List.length_cons,List.range'_succ]

theorem pack_indices {α : Type*} (items : List α) :
    (pack items).2.filterMap PushSnapshot.pushIndex = List.range items.length := by
  simpa only [pack,show (Array.emptyWithCapacity items.length).size = 0 from rfl,List.range_eq_range'] using
    pushLoop_indices items (Array.emptyWithCapacity items.length)

/-- A conservative full-prefix reference-slot exposure for each reached push.
The terminal snapshot contributes no slots. This is not a native-copy claim. -/
def PushSnapshot.prefixSlots (s : PushSnapshot) : ℕ :=
  if s.remaining = 0 then 0 else s.used+1

def prefixSlots (snapshots : List PushSnapshot) : ℕ :=
  (snapshots.map PushSnapshot.prefixSlots).sum

theorem prefixSlots_bound (limit : ℕ) (snapshots : List PushSnapshot)
    (h : ∀ s ∈ snapshots,s.Valid limit) :
    prefixSlots snapshots ≤ snapshots.length*(limit+1) := by
  induction snapshots with
  | nil => simp [prefixSlots]
  | cons s rest ih =>
      have hs := h s (by simp)
      have ht := ih (fun t ht => h t (by simp [ht]))
      have hSlot : PushSnapshot.prefixSlots s ≤ limit+1 := by
        unfold PushSnapshot.prefixSlots
        split
        · omega
        · unfold PushSnapshot.Valid at hs
          omega
      simp only [prefixSlots,List.map_cons,List.sum_cons,List.length_cons] at *
      rw [Nat.add_mul,Nat.one_mul]
      omega

theorem pack_prefixSlots {α : Type*} (items : List α) :
    prefixSlots (pack items).2 ≤ (items.length+1)^2 := by
  have h := prefixSlots_bound items.length (pack items).2 (pack_valid items)
  rw [pack_length] at h
  nlinarith

theorem fromEntries_prefixSlots {α : Type*} (n : ℕ)
    (entries : List (α × BinarySeedPreparationSpace.Trace)) (hEntries : entries.length = n) :
    prefixSlots (pack (entries.map Prod.fst)).2 ≤ (n+1)^2 := by
  simpa only [List.length_map,hEntries] using pack_prefixSlots (entries.map Prod.fst)

theorem fromEntries_pack_control {α : Type*} (n : ℕ)
    (entries : List (α × BinarySeedPreparationSpace.Trace)) (hEntries : entries.length = n) :
    (BinaryLifetimeArray.fromEntries n entries hEntries).1.data =
        (pack (entries.map Prod.fst)).1 ∧
    ((pack (entries.map Prod.fst)).2.filterMap PushSnapshot.pushIndex) = List.range n ∧
    (pack (entries.map Prod.fst)).2.length = n+1 ∧
    ∀ s ∈ (pack (entries.map Prod.fst)).2,
      ∀ value ∈ s.operands n,binaryWordWidth value ≤ binaryWordWidth (n+1) := by
  refine ⟨?_,?_,?_,?_⟩
  · change BinaryLifetimeArray.packEntries n (BinaryLifetimeArray.mapDirect Prod.fst entries) = _
    rw [BinaryLifetimeArray.mapDirect_eq_map]
    exact BinaryLifetimeArray.packEntries_core n _
  · simp only [pack_indices,List.length_map,hEntries]
  · simp only [pack_length,List.length_map,hEntries]
  · simpa only [List.length_map,hEntries] using pack_scalar_width (entries.map Prod.fst)

theorem fromEntries_pack_source_usage {α : Type*} (n : ℕ)
    (entries : List (α × BinarySeedPreparationSpace.Trace)) (hEntries : entries.length = n) :
    (BinaryLifetimeArray.fromEntries n entries hEntries).1.data =
        (BinaryLifetimeListArray.toArrayWithTrace (entries.map Prod.fst)).1 ∧
    BinaryPRGHeapTraceUsage.usage
        (BinaryLifetimeListArray.toArrayWithTrace (entries.map Prod.fst)).2 ≤
      2*(n+1)^2+8 := by
  have hData := (fromEntries_pack_control n entries hEntries).1
  have hSource := pack_source (entries.map Prod.fst)
  have hUsage := BinaryLifetimeListArray.toArrayWithTrace_usage (entries.map Prod.fst)
  simp only [List.length_map,hEntries] at hUsage
  exact ⟨hData.trans hSource,by nlinarith only [hUsage]⟩

theorem read_count {α : Type*} (data : Array α) :
    ((read data).2.filterMap ReadSnapshot.readIndex).length = data.size := by
  rw [read_indices,List.length_reverse,List.length_range]

theorem read_indices_boolean {α β : Type*} (data : Array α) (ruler : List β) (hLength : ruler.length = data.size) :
    ((BooleanArrayIndexEnumeration.enumerateWithTrace ruler).1.reverse.map BinaryCarryCounter.value) =
      (read data).2.filterMap ReadSnapshot.readIndex := by
  rw [List.map_reverse,BooleanArrayIndexEnumeration.enumerate_values,hLength,read_indices]

theorem read_metadata {n : ℕ} {α : Type*} (table : FixedArrayTable n α) (index : Fin n) :
    index.val < table.data.size ∧
      binaryWordWidth table.data.size ≤ binaryWordWidth (n+1) ∧
      binaryWordWidth index.val ≤ binaryWordWidth (n+1) := by
  rw [table.size]
  exact ⟨index.isLt,binaryWordWidth_mono (by omega),binaryWordWidth_mono (by omega)⟩

theorem write_metadata {n : ℕ} {α : Type*} (table : FixedArrayTable n α) (index : Fin n) (value : α) :
    (table.write index value).data.size = n ∧
      binaryWordWidth (table.write index value).data.size ≤ binaryWordWidth (n+1) ∧
      binaryWordWidth index.val ≤ binaryWordWidth (n+1) := by
  rw [(table.write index value).size]
  exact ⟨rfl,binaryWordWidth_mono (by omega),binaryWordWidth_mono (by omega)⟩

theorem build_reservation {n : ℕ} {α : Type*} (produce : Fin n → α) :
    NativeArrayCoreControl.copiedSlots (NativeArrayCoreControl.build produce).2 ≤ 2*(n+1)^2+8 ∧
      (NativeArrayCoreControl.build produce).2.length ≤ n+4 := by
  have h := NativeArrayCoreControl.build_copiedSlots produce
  rw [NativeArrayCoreControl.build_length]
  exact ⟨by nlinarith,by omega⟩

end Blotto.NativeArrayConversionControl
