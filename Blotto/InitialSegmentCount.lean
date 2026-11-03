import Blotto.Model

/-! A downward closed predicate on consecutive finite indices is an exact
prefix. The count is proved by induction without a numerical floor oracle. -/

namespace Blotto
open scoped BigOperators

theorem initialSegment_count {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (hdown : ∀ i j, i ≤ j → P j → P i) :
    ∃ k : ℕ, k ≤ n ∧ (∀ j, P j ↔ j.val < k) ∧
      (∑ j : Fin n, if P j then (1 : ℕ) else 0) = k := by
  induction n with
  | zero => exact ⟨0, le_rfl, fun j => Fin.elim0 j, by simp⟩
  | succ n ih =>
    by_cases hlast : P (Fin.last n)
    · have hall : ∀ j, P j := fun j => hdown j (Fin.last n) (by exact Nat.le_of_lt_succ j.isLt) hlast
      exact ⟨n + 1, le_rfl, fun j => ⟨fun _ => j.isLt, fun _ => hall j⟩, by simp [hall]⟩
    · have hsub : ∀ i j : Fin n, i ≤ j → P j.castSucc → P i.castSucc :=
        fun i j hij hj => hdown _ _ hij hj
      rcases ih (fun j => P j.castSucc) hsub with ⟨k, hkn, hk, hs⟩
      refine ⟨k, by omega, ?_, ?_⟩
      · intro j
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · exact hk i
        · simp only [Fin.val_last]
          constructor
          · exact fun h => (hlast h).elim
          · intro h; omega
      · rw [Fin.sum_univ_castSucc]
        simpa only [hlast, ite_false, add_zero] using hs

end Blotto
