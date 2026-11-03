import Blotto.GeneralPaperBooleanFreshWord

/-! Cumulative selection on stored labeled Boolean count words. Each row
does one fixed-width subtract/borrow scan; failed comparisons continue with
the computed residual word. The returned label is read from that row. -/
namespace Blotto.GeneralPaperBooleanCategoricalSelect
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000

def run {α : Type*} {W : ℕ} : List (α × FixedBinaryWord W) → FixedBinaryWord W → Option α × ℕ
  | [], _ => (none, 2)
  | row :: rest, word =>
    let difference := GeneralPaperBooleanBorrow.subtract word row.2
    if difference.2.1 then (some row.1, difference.2.2 + 6)
    else
      let later := run rest difference.1
      (later.1, difference.2.2 + later.2 + 8)

theorem work {α : Type*} {W : ℕ} (rows : List (α × FixedBinaryWord W)) (word : FixedBinaryWord W) :
    (run rows word).2 ≤ rows.length * (22 * W + 16) + 2 := by
  induction rows generalizing word with
  | nil => simp only [run, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons row rest ih =>
    have hs := GeneralPaperBooleanBorrow.subtract_work word row.2
    have hh := ih (GeneralPaperBooleanBorrow.subtract word row.2).1
    conv => lhs; rw [run]
    split <;> simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;> omega

theorem data {α : Type*} {W : ℕ} (r : ℕ) (label : Fin r → α) (c : Fin r → FixedBinaryWord W)
    (word : FixedBinaryWord W) (rank : Fin (∑ i, (c i).value)) (hValue : word.value = rank.val) :
    (run (List.ofFn (fun i => (label i, c i))) word).1 =
      some (label (GeneralPaperEqualCategoricalSelector.select (fun i => (c i).value) rank)) := by
  induction r generalizing word with
  | zero => have h := rank.isLt; simp at h
  | succ r ih =>
    rw [List.ofFn_succ]
    conv => lhs; rw [run]
    by_cases h : rank.val < (c 0).value
    · have hb : (GeneralPaperBooleanBorrow.subtract word (c 0)).2.1 = true :=
        (GeneralPaperBooleanBorrow.borrow_iff word (c 0)).mpr (by rw [hValue]; exact h)
      rw [hb, ite_eq_left rfl, GeneralPaperEqualCategoricalSelector.select, dite_eq_left h]
    · have hg : (c 0).value ≤ word.value := by rw [hValue]; omega
      have hb : (GeneralPaperBooleanBorrow.subtract word (c 0)).2.1 = false :=
        Bool.eq_false_of_not_eq_true (fun hh => (not_lt_of_ge hg) ((GeneralPaperBooleanBorrow.borrow_iff word (c 0)).mp hh))
      have hr : rank.val - (c 0).value < ∑ j : Fin r, (c j.succ).value := by
        have hh := rank.isLt
        conv at hh => rhs; rw [Fin.sum_univ_succ]
        omega
      let tailRank : Fin (∑ j : Fin r, (c j.succ).value) := ⟨rank.val - (c 0).value, hr⟩
      have hv : (GeneralPaperBooleanBorrow.subtract word (c 0)).1.value = tailRank.val := by
        rw [GeneralPaperBooleanBorrow.difference_value word (c 0) hg, hValue]
      rw [hb, ite_eq_right Bool.false_ne_true]
      have hh := ih (fun j => label j.succ) (fun j => c j.succ)
        (GeneralPaperBooleanBorrow.subtract word (c 0)).1 tailRank hv
      rw [hh, GeneralPaperEqualCategoricalSelector.select, dite_eq_right h]

end Blotto.GeneralPaperBooleanCategoricalSelect
