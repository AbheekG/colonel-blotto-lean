import Blotto.GeneralPaperReferenceSlotConstruction

/-! Raw fixed-word cell semantics for the paper indexed-storage model.
Clients establish disjoint A-bit slot extents; words are addressed by their
encoded location value. Read/write prices include raw address/value copies.
These are RAM primitives, not claims about evaluating function updates in C. -/
namespace Blotto.GeneralPaperRawReferenceMemory
open GeneralPaperReferenceSlotConstruction (Entry)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def Memory (A : ℕ) := ℕ → Option (FixedBinaryWord A)
def empty (A : ℕ) : Memory A := fun _ => none

def write (A : ℕ) (memory : Memory A) (entry : Entry A) : Memory A × ℕ :=
  (Function.update memory entry.location.value (some entry.target),64 * A + 64)

def read (A : ℕ) (memory : Memory A) (location : FixedBinaryWord A) : Option (FixedBinaryWord A) × ℕ :=
  (memory location.value,64 * A + 64)

theorem read_write (A : ℕ) (memory : Memory A) (entry : Entry A) :
    (read A (write A memory entry).1 entry.location).1 = some entry.target := by
  change Function.update memory entry.location.value (some entry.target) entry.location.value = some entry.target
  exact Function.update_self _ _ _

theorem read_write_other (A : ℕ) (memory : Memory A) (entry : Entry A) (location : FixedBinaryWord A)
    (h : location.value ≠ entry.location.value) :
    (read A (write A memory entry).1 location).1 = (read A memory location).1 := by
  change Function.update memory entry.location.value (some entry.target) location.value = memory location.value
  exact Function.update_of_ne h _ _

def install (A : ℕ) (memory : Memory A) : List (Entry A) → Memory A × ℕ
  | [] => (memory,64 * A + 64)
  | entry :: entries =>
    let current := write A memory entry
    let later := install A current.1 entries
    (later.1,current.2 + later.2 + 64 * A + 64)

theorem install_work (A : ℕ) (memory : Memory A) (entries : List (Entry A)) :
    (install A memory entries).2 = entries.length * (128 * A + 128) + 64 * A + 64 := by
  induction entries generalizing memory with
  | nil => simp only [install,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons entry entries ih =>
    change (64 * A + 64) + (install A (write A memory entry).1 entries).2 + 64 * A + 64 = _
    rw [ih]
    simp only [List.length_cons]
    ring

theorem preserves (A : ℕ) (memory : Memory A) (entries : List (Entry A)) (location : FixedBinaryWord A)
    (h : ∀ e ∈ entries,e.location.value ≠ location.value) :
    (read A (install A memory entries).1 location).1 = (read A memory location).1 := by
  induction entries generalizing memory with
  | nil => rfl
  | cons entry entries ih =>
    have hh := h entry (List.mem_cons_self ..)
    have ht := ih (write A memory entry).1 (fun e he => h e (List.mem_cons_of_mem entry he))
    change (read A (install A (write A memory entry).1 entries).1 location).1 = _
    exact ht.trans (read_write_other A memory entry location (Ne.symm hh))

theorem installed (A : ℕ) (memory : Memory A) (entries : List (Entry A))
    (hKeys : (entries.map (fun e => e.location.value)).Nodup) (entry : Entry A) (hEntry : entry ∈ entries) :
    (read A (install A memory entries).1 entry.location).1 = some entry.target := by
  induction entries generalizing memory with
  | nil => cases hEntry
  | cons first entries ih =>
    simp only [List.map_cons,List.nodup_cons] at hKeys
    simp only [List.mem_cons] at hEntry
    rcases hEntry with rfl | hEntry
    · have hLater := preserves A (write A memory entry).1 entries entry.location (by
        intro e he hEq
        exact hKeys.1 (List.mem_map.mpr ⟨e,he,hEq⟩))
      change (read A (install A (write A memory entry).1 entries).1 entry.location).1 = _
      exact hLater.trans (read_write A memory entry)
    · exact ih (write A memory first).1 hKeys.2 hEntry

end Blotto.GeneralPaperRawReferenceMemory
