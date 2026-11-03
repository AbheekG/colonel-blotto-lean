import Blotto.GeneralPaperMeasuredHeaderInstallation

/-! Typed payload-cell semantics for the paper indexed RAM. Addresses are
actual encoded block roots. A cell holds one canonically encoded scalar;
its read/write price includes that scalar's complete encoded length. This
models the paper primitive, not host-language function-update execution. -/
namespace Blotto.GeneralPaperPayloadMemory
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def Memory (α : Type*) := ℕ → Option α
def empty (α : Type*) : Memory α := fun _ => none
abbrev Entry (A : ℕ) (α : Type*) := FixedBinaryWord A × α

def write {α : Type*} (A : ℕ) (encode : α → ℕ) (memory : Memory α) (entry : Entry A α) : Memory α × ℕ :=
  (Function.update memory entry.1.value (some entry.2),encode entry.2 + 64 * A + 64)

def read {α : Type*} (A : ℕ) (encode : α → ℕ) (memory : Memory α) (location : FixedBinaryWord A) : Option α × ℕ :=
  let actual := memory location.value
  (actual,actual.elim 0 encode + 64 * A + 64)

def install {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α) : List (Entry A α) → Memory α × ℕ
  | [] => (memory,64 * (S + A + 1))
  | entry :: entries =>
    let current := write A encode memory entry
    let later := install S A encode current.1 entries
    (later.1,current.2 + later.2 + 64 * (S + A + 1))

theorem install_work {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α) (entries : List (Entry A α)) :
    (install S A encode memory entries).2 = (entries.map (fun e => encode e.2)).sum +
      entries.length * (64 * A + 64 + 64 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction entries generalizing memory with
  | nil => simp only [install,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons entry entries ih =>
    change (encode entry.2 + 64 * A + 64) + (install S A encode (write A encode memory entry).1 entries).2 +
      64 * (S + A + 1) = _
    rw [ih]
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    ring

theorem preserves {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α) (entries : List (Entry A α))
    (location : FixedBinaryWord A) (h : ∀ e ∈ entries,e.1.value ≠ location.value) :
    (install S A encode memory entries).1 location.value = memory location.value := by
  induction entries generalizing memory with
  | nil => rfl
  | cons entry entries ih =>
    have hh := h entry (List.mem_cons_self ..)
    have ht := ih (write A encode memory entry).1 (fun e he => h e (List.mem_cons_of_mem entry he))
    change (install S A encode (write A encode memory entry).1 entries).1 location.value = _
    rw [ht]
    exact Function.update_of_ne (Ne.symm hh) _ _

theorem installed {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α) (entries : List (Entry A α))
    (hKeys : (entries.map (fun e => e.1.value)).Nodup) (entry : Entry A α) (hEntry : entry ∈ entries) :
    (install S A encode memory entries).1 entry.1.value = some entry.2 := by
  induction entries generalizing memory with
  | nil => cases hEntry
  | cons first entries ih =>
    simp only [List.map_cons,List.nodup_cons] at hKeys
    simp only [List.mem_cons] at hEntry
    rcases hEntry with rfl | hEntry
    · have hLater := preserves S A encode (write A encode memory entry).1 entries entry.1 (by
        intro e he hEq
        exact hKeys.1 (List.mem_map.mpr ⟨e,he,hEq⟩))
      change (install S A encode (write A encode memory entry).1 entries).1 entry.1.value = _
      rw [hLater]
      exact Function.update_self _ _ _
    · exact ih (write A encode memory first).1 hKeys.2 hEntry

theorem read_installed {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α) (entries : List (Entry A α))
    (hKeys : (entries.map (fun e => e.1.value)).Nodup) (entry : Entry A α) (hEntry : entry ∈ entries) :
    (read A encode (install S A encode memory entries).1 entry.1).1 = some entry.2 ∧
      (read A encode (install S A encode memory entries).1 entry.1).2 = encode entry.2 + 64 * A + 64 := by
  have h := installed S A encode memory entries hKeys entry hEntry
  simp only [read,h,Option.elim_some,and_self]

end Blotto.GeneralPaperPayloadMemory
