import Blotto.WordMachineWordHeight

/-! Operand certificates along the actual capped interpreter's visited
control path. Pending digits reuse one denominator; neither this certificate
nor the runtime needs to construct the specification tree. -/

namespace Blotto

namespace WordCursor

def Bounded {S : Type*} (I : S → Prop) (w : ℕ) : WordCursor S → Prop
  | .state s => I s
  | .coin a b _ _ upper lower => (a < 2 ^ w ∧ b < 2 ^ w) ∧ I upper ∧ I lower

end WordCursor

namespace WordStateMachine

def RunWordsBounded {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (w R : ℕ)
    (cursor : WordCursor S) (bits : Fin R → Bool) : Prop :=
  match cursor with
  | .state s =>
    I s ∧ match _hs : m.step s with
    | .done _ => True
    | .ask a b hb hab upper lower => m.RunWordsBounded I w R (.coin a b hb hab upper lower) bits
  | .coin a b hb hab upper lower =>
    (a < 2 ^ w ∧ b < 2 ^ w) ∧ 2 * a < 2 ^ (w + 1) ∧
      if a = 0 then m.RunWordsBounded I w R (.state lower) bits else
      if b ≤ a then m.RunWordsBounded I w R (.state upper) bits else
        match R with
        | 0 => True
        | r + 1 =>
          if bits 0 = denominatorDigit a b then
            m.RunWordsBounded I w r (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (Fin.tail bits)
          else m.RunWordsBounded I w r (.state (if bits 0 then lower else upper)) (Fin.tail bits)
termination_by (R, m.cursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    omega
  all_goals omega

theorem runCursor_wordsBounded {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (w : ℕ)
    (hWords : ∀ s, I s → (m.step s).WordsHeight w)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R : ℕ) (cursor : WordCursor S) (bits : Fin R → Bool) (hCursor : cursor.Bounded I w) :
    m.RunWordsBounded I w R cursor bits := by
  cases hCursorEq : cursor with
  | state s =>
    rw [hCursorEq] at hCursor
    unfold RunWordsBounded
    refine ⟨hCursor, ?_⟩
    cases ht : m.step s with
    | done x => trivial
    | ask a b hb hab upper lower =>
      have hw := hWords s hCursor
      have hc := hClosed s hCursor
      rw [ht] at hw hc
      exact m.runCursor_wordsBounded I w hWords hClosed R (.coin a b hb hab upper lower) bits ⟨hw, hc⟩
  | coin a b hb hab upper lower =>
    rw [hCursorEq] at hCursor
    unfold RunWordsBounded
    refine ⟨hCursor.1, coin_doubling_height a w hCursor.1.1, ?_⟩
    by_cases ha : a = 0
    · rw [ite_eq_left ha]
      exact m.runCursor_wordsBounded I w hWords hClosed R (.state lower) bits hCursor.2.2
    rw [ite_eq_right ha]
    by_cases hba : b ≤ a
    · rw [ite_eq_left hba]
      exact m.runCursor_wordsBounded I w hWords hClosed R (.state upper) bits hCursor.2.1
    rw [ite_eq_right hba]
    cases R with
    | zero => trivial
    | succ r =>
      dsimp only
      by_cases hd : bits 0 = denominatorDigit a b
      · rw [ite_eq_left hd]
        exact m.runCursor_wordsBounded I w hWords hClosed r
          (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower)
          (Fin.tail bits) ⟨⟨coin_residual_height a b w hab hCursor.1.2, hCursor.1.2⟩, hCursor.2⟩
      · rw [ite_eq_right hd]
        apply m.runCursor_wordsBounded I w hWords hClosed r _ (Fin.tail bits)
        by_cases hbit : bits 0 = true
        · simpa only [hbit, ite_true, WordCursor.Bounded] using hCursor.2.2
        · simpa [hbit, WordCursor.Bounded] using hCursor.2.1
termination_by (R, m.cursorRank cursor)
decreasing_by
  all_goals simp only [hCursorEq, cursorRank]
  · have hp := m.progress s
    rw [ht] at hp
    omega
  all_goals omega

end WordStateMachine
end Blotto
