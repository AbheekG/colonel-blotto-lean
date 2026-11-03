import Blotto.RealStateMachineCounts

/-! Per-callback primitive allowances compose along the actual indexed state
path. Uniform/control and physical container costs may be priced separately;
this observer is not injected into the production runtime. -/

namespace Blotto.RealStateMachine
open scoped Classical

noncomputable def callbackWork {S α : Type*} (m : RealStateMachine S α) (charge : S → ℕ)
    (C : ℕ) (seed : Fin C → ℝ) (s : S) (pos : ℕ) (_hpos : pos ≤ C) : ℕ :=
  charge s + match m.step s with
  | .done _ => 0
  | .ask p _ upper lower =>
    if hRead : pos < C then
      m.callbackWork charge C seed (if seed ⟨pos, hRead⟩ ≤ p then upper else lower) (pos + 1) (by omega)
    else 0
termination_by C - pos
decreasing_by omega

theorem callbackWork_visits {S α : Type*} (m : RealStateMachine S α) (charge : S → ℕ) (bound : ℕ)
    (hCharge : ∀ s, charge s ≤ bound) (C : ℕ) (seed : Fin C → ℝ) (s : S) (pos : ℕ) (hpos : pos ≤ C) :
    m.callbackWork charge C seed s pos hpos ≤ bound * m.visits C seed s pos hpos := by
  unfold callbackWork visits
  cases hs : m.step s with
  | done x => simpa only [Nat.add_zero, Nat.mul_one] using hCharge s
  | ask p hp upper lower =>
    dsimp only
    split
    · rename_i hRead
      split
      · have ih := m.callbackWork_visits charge bound hCharge C seed upper (pos + 1) (by omega)
        have hc := hCharge s
        nlinarith
      · have ih := m.callbackWork_visits charge bound hCharge C seed lower (pos + 1) (by omega)
        have hc := hCharge s
        nlinarith
    · simpa only [Nat.add_zero, Nat.mul_one] using hCharge s
termination_by C - pos
decreasing_by all_goals omega

theorem callbackWork_rank {S α : Type*} (m : RealStateMachine S α) (charge : S → ℕ) (bound : ℕ)
    (hCharge : ∀ s, charge s ≤ bound) (C : ℕ) (seed : Fin C → ℝ) (s : S) :
    m.callbackWork charge C seed s 0 (Nat.zero_le _) ≤ bound * (m.rank s + 1) :=
  (m.callbackWork_visits charge bound hCharge C seed s 0 (Nat.zero_le _)).trans
    (Nat.mul_le_mul_left bound (m.visits_bound C seed s 0 (Nat.zero_le _)))

theorem callbackWork_request_rank {S α : Type*} (m : RealStateMachine S α) (charge : S → ℕ) (bound : ℕ)
    (hCharge : ∀ s, charge s ≤ bound) (hDone : ∀ s x, m.step s = .done x → charge s = 0)
    (C : ℕ) (seed : Fin C → ℝ) (s : S) (pos : ℕ) (hpos : pos ≤ C) :
    m.callbackWork charge C seed s pos hpos ≤ bound * m.rank s := by
  unfold callbackWork
  cases hs : m.step s with
  | done x => rw [hDone s x hs]; exact Nat.zero_le _
  | ask p hp upper lower =>
    have hProgress := m.progress s
    rw [hs] at hProgress
    have hChargeS := hCharge s
    dsimp only
    split
    · rename_i hRead
      split
      · have ih := m.callbackWork_request_rank charge bound hCharge hDone C seed upper (pos + 1) (by omega)
        have hRanks : m.rank upper + 1 ≤ m.rank s := by omega
        have hMul := Nat.mul_le_mul_left bound hRanks
        nlinarith
      · have ih := m.callbackWork_request_rank charge bound hCharge hDone C seed lower (pos + 1) (by omega)
        have hRanks : m.rank lower + 1 ≤ m.rank s := by omega
        have hMul := Nat.mul_le_mul_left bound hRanks
        nlinarith
    · have hRank : 1 ≤ m.rank s := by omega
      have hMul := Nat.mul_le_mul_left bound hRank
      omega
termination_by C - pos
decreasing_by all_goals omega

end Blotto.RealStateMachine
