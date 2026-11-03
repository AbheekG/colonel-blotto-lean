import Blotto.RationalArrayConstructionWork
import Blotto.FixedArrayTable

/-! Conservative payload-word traffic for array construction and patching.
Every push may copy the entire prefix; every set may copy the entire current
array and its new value. The observer follows actual intermediate tables.
Exclusivity, physical addresses, allocator records and space remain separate. -/

namespace Blotto
open scoped BigOperators

def wordArrayCopyWork {α : Type*} (words : α → ℕ) : List α → ℕ → ℕ
  | [], _ => 0
  | x :: rest, prefixWords => 2 * (prefixWords + words x) + wordArrayCopyWork words rest (prefixWords + words x)

theorem wordArrayCopyWork_bound {α : Type*} (words : α → ℕ) (row : List α) (prefixWords : ℕ) :
    wordArrayCopyWork words row prefixWords ≤ 2 * row.length * (prefixWords + (row.map words).sum) := by
  induction row generalizing prefixWords with
  | nil => simp [wordArrayCopyWork]
  | cons x rest ih =>
    have ht := ih (prefixWords + words x)
    simp only [wordArrayCopyWork, List.length_cons, List.map_cons, List.sum_cons]
    calc
      _ ≤ 2 * (prefixWords + words x) + 2 * rest.length * (prefixWords + words x + (rest.map words).sum) := Nat.add_le_add_left ht _
      _ ≤ 2 * (prefixWords + words x + (rest.map words).sum) + 2 * rest.length * (prefixWords + words x + (rest.map words).sum) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 (by omega)) _
      _ = _ := by ring

theorem wordArrayCopyWork_uniform_bound {α : Type*} (words : α → ℕ) (row : List α) (W : ℕ)
    (h : ∀ x ∈ row, words x ≤ W) : wordArrayCopyWork words row 0 ≤ 2 * row.length * row.length * W := by
  have hSum : (row.map words).sum ≤ row.length * W := by
    calc
      _ ≤ (row.map (fun _ => W)).sum := List.sum_le_sum h
      _ = _ := by simp
  have hp := wordArrayCopyWork_bound words row 0
  simp only [Nat.zero_add] at hp
  exact (hp.trans (Nat.mul_le_mul_left _ hSum)).trans_eq (by ring)

namespace FixedArrayTable

def payloadWordSum {n : ℕ} {α : Type*} (words : α → ℕ) (a : FixedArrayTable n α) : ℕ :=
  ∑ j : Fin n, words (a.read j)

theorem payloadWordSum_bound {n : ℕ} {α : Type*} (words : α → ℕ) (a : FixedArrayTable n α)
    (W : ℕ) (h : ∀ j, words (a.read j) ≤ W) : a.payloadWordSum words ≤ n * W := by
  calc
    _ ≤ ∑ _j : Fin n, W := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

theorem write_words_bound {n : ℕ} {α : Type*} (words : α → ℕ) (a : FixedArrayTable n α)
    (W : ℕ) (h : ∀ j, words (a.read j) ≤ W) (j : Fin n) (value : α) (hv : words value ≤ W) :
    ∀ k, words ((a.write j value).read k) ≤ W := by
  intro k
  rw [read_write]
  split <;> first | exact hv | exact h k

def patchCopyWork {n : ℕ} {α : Type*} (words : α → ℕ) (a : FixedArrayTable n α) : List (Fin n × α) → ℕ
  | [] => 0
  | e :: rest => 2 * (a.payloadWordSum words + words e.2) + (a.write e.1 e.2).patchCopyWork words rest

theorem patchCopyWork_bound {n : ℕ} {α : Type*} (words : α → ℕ) (a : FixedArrayTable n α)
    (es : List (Fin n × α)) (W : ℕ) (h : ∀ j, words (a.read j) ≤ W)
    (hAssigned : ∀ e ∈ es, words e.2 ≤ W) :
    a.patchCopyWork words es ≤ es.length * (2 * (n + 1) * W) := by
  induction es generalizing a with
  | nil => exact Nat.zero_le _
  | cons e rest ih =>
    have he := hAssigned e (by simp)
    have ht := ih (a.write e.1 e.2) (a.write_words_bound words W h e.1 e.2 he)
      (fun e he => hAssigned e (List.mem_cons_of_mem _ he))
    have hs := a.payloadWordSum_bound words W h
    simp only [patchCopyWork, List.length_cons]
    calc
      _ ≤ 2 * (n * W + W) + rest.length * (2 * (n + 1) * W) :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.add_le_add hs he)) ht
      _ = _ := by ring

end FixedArrayTable
end Blotto
