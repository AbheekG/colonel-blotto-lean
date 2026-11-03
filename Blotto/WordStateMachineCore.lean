import Blotto.WordChoiceLaw

/-! A state-based shared-cap interpreter. The transition procedure is queried
only when a new coin is requested; fixed-denominator digits are then processed
without re-running it. Ranking is used solely for termination/proofs, and no
choice tree is constructed by the runtime interpreter. The primary loop keeps
one input reader and an index, and every recursive call is in tail position.
The earlier cursor evaluator remains a refinement reference. -/

namespace Blotto

inductive WordTransition (S α : Type*) where
  | done (value : α)
  | ask (numerator denominator : ℕ) (denominator_pos : 0 < denominator)
      (normalized : numerator ≤ denominator) (upper lower : S)

structure WordStateMachine (S α : Type*) where
  step : S → WordTransition S α
  rank : S → ℕ
  progress : ∀ s, match step s with
    | .done _ => True
    | .ask _ _ _ _ upper lower => rank upper < rank s ∧ rank lower < rank s

inductive WordCursor (S : Type*) where
  | state (s : S)
  | coin (numerator denominator : ℕ) (denominator_pos : 0 < denominator)
      (normalized : numerator ≤ denominator) (upper lower : S)

namespace WordStateMachine

def specification {S α : Type*} (m : WordStateMachine S α) (s : S) : WordChoiceTree α :=
  match _hs : m.step s with
  | .done value => .leaf value
  | .ask a b hb hab upper lower => .fork a b hb hab (m.specification upper) (m.specification lower)
termination_by m.rank s
decreasing_by
  all_goals have hp := m.progress s
  all_goals rw [_hs] at hp
  all_goals omega

def cursorLevel {S α : Type*} (m : WordStateMachine S α) : WordCursor S → ℕ
  | .state s => m.rank s
  | .coin _ _ _ _ upper lower => 1 + max (m.rank upper) (m.rank lower)

def cursorRank {S α : Type*} (m : WordStateMachine S α) : WordCursor S → ℕ
  | .state s => 2 * m.rank s + 1
  | .coin _ _ _ _ upper lower => 2 * (1 + max (m.rank upper) (m.rank lower))

def cursorSpecification {S α : Type*} (m : WordStateMachine S α) : WordCursor S → WordChoiceTree α
  | .state s => m.specification s
  | .coin a b hb hab upper lower => .fork a b hb hab (m.specification upper) (m.specification lower)

def runCursor {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (cursor : WordCursor S)
    (bits : Fin R → Bool) : Option α × ℕ :=
  match cursor with
  | .state s =>
    match _hs : m.step s with
    | .done value => (some value, 0)
    | .ask a b hb hab upper lower => m.runCursor R (.coin a b hb hab upper lower) bits
  | .coin a b hb hab upper lower =>
    if a = 0 then m.runCursor R (.state lower) bits else
      if b ≤ a then m.runCursor R (.state upper) bits else
        match R with
        | 0 => (none, 0)
        | r + 1 =>
          if bits 0 = denominatorDigit a b then
            let result := m.runCursor r (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (Fin.tail bits)
            (result.1, result.2 + 1)
          else
            let result := m.runCursor r (.state (if bits 0 then lower else upper)) (Fin.tail bits)
            (result.1, result.2 + 1)
termination_by (R, m.cursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    omega
  all_goals omega

def inputWindow {N : ℕ} (bits : Fin N → Bool) (pos length : ℕ) (h : pos + length ≤ N) : Fin length → Bool :=
  fun j => bits ⟨pos + j.val, by omega⟩

def offsetConsumed {α : Type*} (pos : ℕ) (result : Option α × ℕ) : Option α × ℕ :=
  (result.1, pos + result.2)

def runCursorIndexed {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) : Option α × ℕ :=
  match cursor with
  | .state s =>
    match _hs : m.step s with
    | .done value => (some value, pos)
    | .ask a b hb hab upper lower => m.runCursorIndexed N bits (.coin a b hb hab upper lower) pos hpos
  | .coin a b hb hab upper lower =>
    if a = 0 then m.runCursorIndexed N bits (.state lower) pos hpos else
      if b ≤ a then m.runCursorIndexed N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let bit := bits ⟨pos, hRead⟩
          if bit = denominatorDigit a b then
            m.runCursorIndexed N bits
              (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos + 1) (by omega)
          else m.runCursorIndexed N bits (.state (if bit then lower else upper)) (pos + 1) (by omega)
        else (none, pos)
termination_by (N - pos, m.cursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    omega
  all_goals omega

def runNumeric {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (bits : Fin R → Bool) : Option α × ℕ :=
  m.runCursorIndexed R bits (.state s) 0 (Nat.zero_le R)

theorem specification_height {S α : Type*} (m : WordStateMachine S α) (s : S) :
    (m.specification s).height ≤ m.rank s := by
  have hAll : ∀ n, ∀ s : S, m.rank s = n → (m.specification s).height ≤ m.rank s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      unfold specification
      split
      · simp [WordChoiceTree.height]
      · rename_i a b hb hab upper lower hs
        have hp := m.progress s
        rw [hs] at hp
        have hu := ih (m.rank upper) (by omega) upper rfl
        have hl := ih (m.rank lower) (by omega) lower rfl
        change 1 + max (m.specification upper).height (m.specification lower).height ≤ m.rank s
        omega
  exact hAll (m.rank s) s rfl

theorem cursorSpecification_height {S α : Type*} (m : WordStateMachine S α) (cursor : WordCursor S) :
    (m.cursorSpecification cursor).height ≤ m.cursorLevel cursor := by
  cases cursor with
  | state s => exact m.specification_height s
  | coin a b hb hab upper lower =>
    change 1 + max (m.specification upper).height (m.specification lower).height ≤ 1 + max (m.rank upper) (m.rank lower)
    exact Nat.add_le_add_left (max_le_max (m.specification_height upper) (m.specification_height lower)) 1

end WordStateMachine
end Blotto
