import Blotto.BinaryPRGWordControllerWordWalk
import Blotto.BinaryOverlapInputPreparation

/-! A ghost native-table view connects the concrete Boolean-address table
backend to existing resource/register/coupling specifications.  The view may
assemble mathematical ofNat addresses; it is explicitly noncomputable proof
data and is never called by lookup, update or Boolean-counter traversal.
Every concrete read/write and prepared source table has exact native words.
This supplies refinement, not a price for unchanged native callers. -/

namespace Blotto.BinaryPRGWordControllerWordStoreView
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerWordWalk

theorem address_bits_eq {width : ℕ} (first second : FixedBinaryWord width)
    (h : first.value = second.value) : first.bits = second.bits :=
  BinaryBorrowWord.littleValue_injective first.bits second.bits (first.size.trans second.size.symm) h

theorem lookup_congr {width : ℕ} (tree : Tree width) (first second : FixedBinaryWord width)
    (h : first.value = second.value) : lookup tree first = lookup tree second := by
  unfold lookup
  rw [address_bits_eq first second h]

noncomputable def view (store : Store) (n : ℕ) (_h : n = store.cap.value) : FixedArrayTable n SignedWord :=
  FixedArrayTable.ofFn (fun j => lookup store.tree (FixedBinaryWord.ofNat store.width j.val))

theorem view_read (store : Store) (n : ℕ) (h : n = store.cap.value) (j : Fin n) :
    (view store n h).read j = lookup store.tree (FixedBinaryWord.ofNat store.width j.val) :=
  FixedArrayTable.read_ofFn _ _

theorem address_room (store : Store) (address : FixedBinaryWord store.width)
    (h : address.value < store.cap.value) : address.value < 2^store.width :=
  h.trans (cap_room store)

theorem view_read_address (store : Store) (n : ℕ) (hCount : n = store.cap.value)
    (address : FixedBinaryWord store.width) (h : address.value < n) :
    (view store n hCount).read ⟨address.value, h⟩ = lookup store.tree address := by
  rw [view_read]
  exact lookup_congr _ _ _ (FixedBinaryWord.value_ofNat store.width address.value
    (address_room store address (by simpa only [hCount] using h)))

theorem read_view (store : Store) (n : ℕ) (hCount : n = store.cap.value)
    (address : FixedBinaryWord store.width) (h : address.value < n) :
    BinaryPRGWordControllerWordStore.read store address = some ((view store n hCount).read ⟨address.value, h⟩) := by
  unfold BinaryPRGWordControllerWordStore.read
  have hGuard := (BinaryIndexWord.lt_value address store.cap).mpr (by simpa only [hCount] using h)
  rw [hGuard, ite_eq_left rfl, view_read_address]

theorem view_update (store : Store) (n : ℕ) (hCount : n = store.cap.value)
    (address : FixedBinaryWord store.width) (h : address.value < n) (word : SignedWord) :
    view (update store address word) n hCount = (view store n hCount).write ⟨address.value, h⟩ word := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [view, FixedArrayTable.read_ofFn, FixedArrayTable.read_write, update]
  rw [lookup_write, FixedBinaryWord.value_ofNat store.width j.val (by
    have hj : j.val < store.cap.value := by simpa only [hCount] using j.isLt
    exact hj.trans (cap_room store))]
  have hIndex : j = (⟨address.value, h⟩ : Fin n) ↔ j.val = address.value := Fin.ext_iff
  simp only [hIndex]

def ofTable {n : ℕ} (table : FixedArrayTable n SignedWord) : Store :=
  prepare BinaryRationalOpcode.zero (List.ofFn table.read)

theorem ofTable_count {n : ℕ} (table : FixedArrayTable n SignedWord) :
    n = (ofTable table).cap.value := by
  unfold ofTable
  rw [prepare_cap, List.length_ofFn]

theorem view_ofTable {n : ℕ} (table : FixedArrayTable n SignedWord) :
    view (ofTable table) n (ofTable_count table) = table := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  rw [view_read]
  unfold ofTable
  rw [prepare_lookup, FixedBinaryWord.value_ofNat]
  · simp [List.getD_eq_getElem?_getD, j.isLt]
  · have hCount := ofTable_count table
    have hRoom := cap_room (ofTable table)
    rw [← hCount] at hRoom
    exact j.isLt.trans hRoom

theorem ofTable_read {n : ℕ} (table : FixedArrayTable n SignedWord)
    (address : FixedBinaryWord (ofTable table).width) (h : address.value < n) :
    BinaryPRGWordControllerWordStore.read (ofTable table) address = some (table.read ⟨address.value, h⟩) := by
  rw [read_view _ n (ofTable_count table) address h, view_ofTable]

theorem ofTable_write {n : ℕ} (table : FixedArrayTable n SignedWord)
    (address : FixedBinaryWord (ofTable table).width) (h : address.value < n) (word : SignedWord) :
    view (update (ofTable table) address word) n (ofTable_count table) = table.write ⟨address.value, h⟩ word := by
  rw [view_update, view_ofTable]

theorem ofTable_toList {n : ℕ} (table : FixedArrayTable n SignedWord) :
    (toListWithWork (ofTable table)).1 = List.ofFn table.read :=
  toListWithWork_prepare _ _

theorem view_canonical (store : Store) (n : ℕ) (hCount : n = store.cap.value)
    (hWords : ∀ address : FixedBinaryWord store.width, address.value < store.cap.value →
      CanonicalWord (lookup store.tree address)) :
    ∀ j, CanonicalWord ((view store n hCount).read j) := by
  intro j
  rw [view_read]
  have hjCap : j.val < store.cap.value := by simpa only [hCount] using j.isLt
  have hRoom : j.val < 2^store.width := hjCap.trans (cap_room store)
  exact hWords _ (by rw [FixedBinaryWord.value_ofNat store.width j.val hRoom]; simpa only [hCount] using j.isLt)

end Blotto.BinaryPRGWordControllerWordStoreView
