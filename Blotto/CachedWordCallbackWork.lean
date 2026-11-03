import Blotto.CachedWordControllerCounts
import Blotto.WordMachineWorkPotential

/-! State-dependent callback prices follow the production Boolean-word loop.
Exact weighted-work equality is stronger than equality of callback counts:
it preserves arbitrary state prices and one-time preparation potentials. -/

namespace Blotto.WordStateMachine

def cachedCallbackWork {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .state s => charge s + match _hs : m.step s with
    | .done _ => 0
    | .ask a b hb hab upper lower =>
      m.cachedCallbackWork charge N bits (.ofWords a b hb hab upper lower) pos hpos
  | .coin a b hb hab upper lower =>
    if hz : a.isZero = true then m.cachedCallbackWork charge N bits (.state lower) pos hpos else
      if he : a.same b = true then m.cachedCallbackWork charge N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            m.cachedCallbackWork charge N bits (.coin next.2 b hb (a.coinStep_normalized b hlt).le upper lower)
              (pos + 1) (by omega)
          else m.cachedCallbackWork charge N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
            (pos + 1) (by omega)
        else 0
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem cachedCallbackWork_refines {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ) (N : ℕ)
    (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCallbackWork charge N bits cursor pos hpos = m.indexedCallbackWork charge N bits cursor.reference pos hpos := by
  cases cursor with
  | state s =>
    conv_lhs => unfold cachedCallbackWork
    conv_rhs => rw [CachedWordCursor.reference]; unfold indexedCallbackWork
    cases hs : m.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      have h := m.cachedCallbackWork_refines charge N bits (.ofWords a b hb hab upper lower) pos hpos
      simpa only [CachedWordCursor.reference_ofWords] using congrArg (fun w => charge s + w) h
  | coin a b hb hab upper lower =>
    conv_lhs => unfold cachedCallbackWork
    conv_rhs => rw [CachedWordCursor.reference]; unfold indexedCallbackWork
    have hZero : a.isZero = true ↔ a.value = 0 := a.isZero_value
    have hSame : a.same b = true ↔ b.value ≤ a.value := by
      rw [a.same_value b]
      constructor
      · intro he; rw [he]
      · intro he; exact Nat.le_antisymm hab he
    simp only [hZero, hSame]
    by_cases hz : a.value = 0
    · simp only [dite_eq_left hz, ite_eq_left hz]
      exact m.cachedCallbackWork_refines charge N bits (.state lower) pos hpos
    · simp only [dite_eq_right hz, ite_eq_right hz]
      by_cases he : b.value ≤ a.value
      · simp only [dite_eq_left he, ite_eq_left he]
        exact m.cachedCallbackWork_refines charge N bits (.state upper) pos hpos
      · simp only [dite_eq_right he, ite_eq_right he]
        by_cases hRead : pos < N
        · simp only [dite_eq_left hRead, FixedBinaryWord.coinStep_digit]
          have hlt : a.value < b.value := lt_of_not_ge he
          by_cases hd : bits ⟨pos, hRead⟩ = denominatorDigit a.value b.value
          · simp only [ite_eq_left hd]
            have h := m.cachedCallbackWork_refines charge N bits
              (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
            simpa only [CachedWordCursor.reference, a.coinStep_residual b hlt] using h
          · simp only [ite_eq_right hd]
            exact m.cachedCallbackWork_refines charge N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

def runCachedCallbackWork {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (R : ℕ) (s : S) (bits : Fin R → Bool) : ℕ :=
  m.cachedCallbackWork charge R bits (.state s) 0 (Nat.zero_le R)

theorem runCachedCallbackWork_eq {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (R : ℕ) (s : S) (bits : Fin R → Bool) :
    m.runCachedCallbackWork charge R s bits = m.runCallbackWork charge R s bits :=
  m.cachedCallbackWork_refines charge R bits (.state s) 0 (Nat.zero_le R)

theorem cachedCallbackWork_counts {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (bound : ℕ) (hCharge : ∀ s, charge s ≤ bound) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCallbackWork charge N bits cursor pos hpos ≤ bound * (m.cachedCounts N bits cursor pos hpos).callbacks := by
  rw [m.cachedCallbackWork_refines, m.cachedCounts_refines]
  exact m.indexedCallbackWork_counts charge bound hCharge N bits cursor.reference pos hpos

theorem runCachedCallbackWork_potential {S α : Type*} (m : WordStateMachine S α)
    (charge potential : S → ℕ) (hCost : m.WorkPotential charge potential)
    (R : ℕ) (s : S) (bits : Fin R → Bool) :
    m.runCachedCallbackWork charge R s bits ≤ potential s := by
  rw [m.runCachedCallbackWork_eq]
  exact m.runCallbackWork_potential charge potential hCost R s bits

theorem runCachedCallbackWork_bound {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (bound : ℕ) (hCharge : ∀ s, charge s ≤ bound) (R C : ℕ) (s : S)
    (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.runCachedCallbackWork charge R s bits ≤ bound * (C + 1) := by
  rw [m.runCachedCallbackWork_eq]
  exact m.runCallbackWork_bound charge bound hCharge R C s hRank bits

theorem runCachedCallbackWork_zero_initial_rank {S α : Type*} (m : WordStateMachine S α)
    (charge : S → ℕ) (bound : ℕ) (hCharge : ∀ s, charge s ≤ bound)
    (R : ℕ) (s : S) (hZero : charge s = 0) (bits : Fin R → Bool) :
    m.runCachedCallbackWork charge R s bits ≤ bound * m.rank s := by
  rw [m.runCachedCallbackWork_eq]
  exact m.runCallbackWork_zero_initial_rank charge bound hCharge R s hZero bits

end Blotto.WordStateMachine
