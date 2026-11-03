import Blotto.GeneralPaperSelectedLayoutLifetimeRates

/-! Finite encoded ownership of the actual paper RAM map. A write replaces
one cell and adds at most its encoded payload to the old reserve. Prefix
installation bounds require neither key uniqueness nor a supplied owner
certificate. This concerns the paper indexed RAM, not host function closures. -/
namespace Blotto.GeneralPaperPayloadMemoryOwnership
open GeneralPaperPayloadMemory (Memory Entry empty write install)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def cellSize {α : Type*} (encode : α → ℕ) (memory : Memory α) (key : ℕ) : ℕ :=
  (memory key).elim 0 encode

def Bounded {α : Type*} (encode : α → ℕ) (memory : Memory α) (B : ℕ) : Prop :=
  ∃ keys : Finset ℕ,(∀ key,memory key ≠ none → key ∈ keys) ∧ ∑ key ∈ keys,cellSize encode memory key ≤ B

def payload {α : Type*} {A : ℕ} (encode : α → ℕ) (entries : List (Entry A α)) : ℕ :=
  (entries.map (fun entry => encode entry.2)).sum

theorem mono {α : Type*} (encode : α → ℕ) (memory : Memory α) (B C : ℕ)
    (h : Bounded encode memory B) (hBC : B ≤ C) : Bounded encode memory C := by
  obtain ⟨keys,hSupport,hSize⟩ := h
  exact ⟨keys,hSupport,hSize.trans hBC⟩

theorem empty_bounded {α : Type*} (encode : α → ℕ) : Bounded encode (empty α) 0 := by
  refine ⟨∅,?_,?_⟩
  · intro key h
    exact False.elim (h rfl)
  · simp only [Finset.sum_empty,le_refl]

theorem write_bounded {α : Type*} (A : ℕ) (encode : α → ℕ) (memory : Memory α)
    (B : ℕ) (h : Bounded encode memory B) (entry : Entry A α) :
    Bounded encode (write A encode memory entry).1 (B + encode entry.2) := by
  classical
  obtain ⟨keys,hSupport,hSize⟩ := h
  refine ⟨insert entry.1.value (keys.erase entry.1.value),?_,?_⟩
  · intro key hPresent
    by_cases hKey : key = entry.1.value
    · exact hKey ▸ Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_erase.mpr
      refine ⟨hKey,hSupport key ?_⟩
      change Function.update memory entry.1.value (some entry.2) key ≠ none at hPresent
      have hEq : Function.update memory entry.1.value (some entry.2) key = memory key :=
        Function.update_of_ne hKey _ _
      rw [hEq] at hPresent
      exact hPresent
  · rw [Finset.sum_insert (by simp)]
    have hCurrent : cellSize encode (write A encode memory entry).1 entry.1.value = encode entry.2 := by
      have hEq : Function.update memory entry.1.value (some entry.2) entry.1.value = some entry.2 :=
        Function.update_self _ _ _
      exact congrArg (fun value : Option α => value.elim 0 encode) hEq
    have hTail : ∑ key ∈ keys.erase entry.1.value,cellSize encode (write A encode memory entry).1 key =
        ∑ key ∈ keys.erase entry.1.value,cellSize encode memory key := by
      apply Finset.sum_congr rfl
      intro key hk
      have hKey := (Finset.mem_erase.mp hk).1
      have hEq : Function.update memory entry.1.value (some entry.2) key = memory key :=
        Function.update_of_ne hKey _ _
      exact congrArg (fun value : Option α => value.elim 0 encode) hEq
    rw [hCurrent,hTail]
    have hSubset : ∑ key ∈ keys.erase entry.1.value,cellSize encode memory key ≤ ∑ key ∈ keys,cellSize encode memory key :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => Nat.zero_le _)
    omega

theorem install_bounded {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α)
    (B : ℕ) (h : Bounded encode memory B) (entries : List (Entry A α)) :
    Bounded encode (install S A encode memory entries).1 (B + payload encode entries) := by
  induction entries generalizing memory B with
  | nil => simpa only [install,payload,List.map_nil,List.sum_nil,Nat.add_zero] using h
  | cons entry entries ih =>
    have hNext := write_bounded A encode memory B h entry
    have hLater := ih (write A encode memory entry).1 (B + encode entry.2) hNext
    simpa only [install,payload,List.map_cons,List.sum_cons,Nat.add_assoc] using hLater

theorem payload_prefix {α : Type*} (A : ℕ) (encode : α → ℕ) (entries : List (Entry A α)) (depth : ℕ) :
    payload encode (entries.take depth) ≤ payload encode entries := by
  exact GeneralPaperReferenceHeaderSlotArea.sum_sublist _ _ ((List.take_sublist depth entries).map (fun entry => encode entry.2))

theorem prefix_bounded {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α)
    (B : ℕ) (h : Bounded encode memory B) (entries : List (Entry A α)) (depth : ℕ) :
    Bounded encode (install S A encode memory (entries.take depth)).1 (B + payload encode entries) :=
  mono encode _ _ _ (install_bounded S A encode memory B h _) (Nat.add_le_add_left (payload_prefix A encode entries depth) B)

theorem install_append {α : Type*} (S A : ℕ) (encode : α → ℕ) (memory : Memory α)
    (first rest : List (Entry A α)) :
    (install S A encode memory (first ++ rest)).1 = (install S A encode (install S A encode memory first).1 rest).1 := by
  induction first generalizing memory with
  | nil => rfl
  | cons entry entries ih =>
    simpa only [List.cons_append,install] using ih (write A encode memory entry).1

end Blotto.GeneralPaperPayloadMemoryOwnership
