import Blotto.CachedWordCallbackWork

/-! An output-only callback charge follows the cached indexed interpreter.
It is paid exactly once on success and never on cap exhaustion. Producing an
output and pricing it remain separate from controller and backend work. -/

namespace Blotto.WordStateMachine

def emissionCharge {S α : Type*} (m : WordStateMachine S α) (price : α → ℕ) (s : S) : ℕ :=
  match m.step s with
  | .done value => price value
  | .ask _ _ _ _ _ _ => 0

def cachedEmissionWork {S α : Type*} (m : WordStateMachine S α) (price : α → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  m.cachedCallbackWork (m.emissionCharge price) N bits cursor pos hpos

theorem cachedEmissionWork_eq {S α : Type*} (m : WordStateMachine S α) (price : α → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedEmissionWork price N bits cursor pos hpos =
      ((m.runCachedIndexed N bits cursor pos hpos).1.map price).getD 0 := by
  unfold cachedEmissionWork
  cases cursor with
  | state s =>
    conv_lhs => unfold cachedCallbackWork
    conv_rhs => unfold runCachedIndexed
    cases hs : m.step s with
    | done value => simp only [emissionCharge, hs, Option.map_some, Option.getD_some, Nat.add_zero]
    | ask a b hb hab upper lower =>
      simp only [emissionCharge, hs, Nat.zero_add]
      exact m.cachedEmissionWork_eq price N bits (.ofWords a b hb hab upper lower) pos hpos
  | coin a b hb hab upper lower =>
    conv_lhs => unfold cachedCallbackWork
    conv_rhs => unfold runCachedIndexed
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      exact m.cachedEmissionWork_eq price N bits (.state lower) pos hpos
    · simp only [dite_eq_right hz]
      by_cases he : a.same b = true
      · simp only [dite_eq_left he]
        exact m.cachedEmissionWork_eq price N bits (.state upper) pos hpos
      · simp only [dite_eq_right he]
        by_cases hRead : pos < N
        · simp only [dite_eq_left hRead]
          by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
          · simp only [ite_eq_left hd]
            have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
            exact m.cachedEmissionWork_eq price N bits
              (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
          · simp only [ite_eq_right hd]
            exact m.cachedEmissionWork_eq price N bits
              (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        · simp only [dite_eq_right hRead, Option.map_none, Option.getD_none]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem cachedEmissionWork_of_none {S α : Type*} (m : WordStateMachine S α) (price : α → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N)
    (hNone : (m.runCachedIndexed N bits cursor pos hpos).1 = none) :
    m.cachedEmissionWork price N bits cursor pos hpos = 0 := by
  rw [cachedEmissionWork_eq, hNone]
  rfl

theorem cachedEmissionWork_of_some {S α : Type*} (m : WordStateMachine S α) (price : α → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N)
    (value : α) (hSome : (m.runCachedIndexed N bits cursor pos hpos).1 = some value) :
    m.cachedEmissionWork price N bits cursor pos hpos = price value := by
  rw [cachedEmissionWork_eq, hSome]
  rfl

end Blotto.WordStateMachine
