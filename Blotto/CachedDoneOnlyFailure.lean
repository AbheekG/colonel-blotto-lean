import Blotto.CachedWordCallbackWork

/-! A callback charge that is zero on asks vanishes on capped failure.
This follows the production cached indexed loop and does not assume an output
value uniquely determines the final callback state or its price. -/

namespace Blotto.WordStateMachine

theorem cachedCallbackWork_doneOnly_failure {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (hAsk : ∀ state, match m.step state with
      | .done _ => True
      | .ask _ _ _ _ _ _ => charge state = 0)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N)
    (hNone : (m.runCachedIndexed N bits cursor pos hpos).1 = none) :
    m.cachedCallbackWork charge N bits cursor pos hpos = 0 := by
  revert hNone
  cases hCursor : cursor with
  | state state =>
    intro hNone
    conv_lhs => unfold cachedCallbackWork
    cases hs : m.step state with
    | done value =>
      have hr : m.runCachedIndexed N bits (.state state) pos hpos = (some value, pos) := by
        conv_lhs => unfold runCachedIndexed
        rw [hs]
      have hf : (some value : Option α) = none := (congrArg Prod.fst hr).symm.trans hNone
      cases hf
    | ask a b hb hab upper lower =>
      have hc := hAsk state
      rw [hs] at hc
      simp only [hc, Nat.zero_add]
      have hr : m.runCachedIndexed N bits (.state state) pos hpos =
          m.runCachedIndexed N bits (.ofWords a b hb hab upper lower) pos hpos := by
        conv_lhs => unfold runCachedIndexed
        rw [hs]
      have hf : (m.runCachedIndexed N bits (.ofWords a b hb hab upper lower) pos hpos).1 = none :=
        (congrArg Prod.fst hr).symm.trans hNone
      exact m.cachedCallbackWork_doneOnly_failure charge hAsk N bits (.ofWords a b hb hab upper lower) pos hpos hf
  | coin a b hb hab upper lower =>
    intro hNone
    conv_lhs => unfold cachedCallbackWork
    rw [runCachedIndexed] at hNone
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz] at hNone ⊢
      exact m.cachedCallbackWork_doneOnly_failure charge hAsk N bits (.state lower) pos hpos hNone
    · simp only [dite_eq_right hz] at hNone ⊢
      by_cases he : a.same b = true
      · simp only [dite_eq_left he] at hNone ⊢
        exact m.cachedCallbackWork_doneOnly_failure charge hAsk N bits (.state upper) pos hpos hNone
      · simp only [dite_eq_right he] at hNone ⊢
        by_cases hRead : pos < N
        · simp only [dite_eq_left hRead] at hNone ⊢
          by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
          · simp only [ite_eq_left hd] at hNone ⊢
            have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
            exact m.cachedCallbackWork_doneOnly_failure charge hAsk N bits
              (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega) hNone
          · simp only [ite_eq_right hd] at hNone ⊢
            exact m.cachedCallbackWork_doneOnly_failure charge hAsk N bits
              (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega) hNone
        · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [hCursor, cachedCursorRank]
  all_goals first
    | (have hp := m.progress state; rw [hs] at hp; simp only [CachedWordCursor.ofWords]; omega)
    | omega

end Blotto.WordStateMachine
