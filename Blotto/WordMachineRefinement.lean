import Blotto.WordMachineIndexedRefinement

/-! The state-machine interpreter refines the proof tree exactly, including
bit consumption. The operational side calls transitions only on visited
states and never calls the tree-construction specification. -/

namespace Blotto.WordStateMachine

theorem runCursor_refines {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (cursor : WordCursor S)
    (bits : Fin R → Bool) : m.runCursor R cursor bits = (m.cursorSpecification cursor).sample R bits := by
  cases cursor with
  | state s =>
    conv_lhs => unfold runCursor
    cases hs : m.step s with
    | done value =>
      have ht : m.specification s = WordChoiceTree.leaf value := by
        conv_lhs => unfold specification
        rw [hs]
      change (some value, 0) = (m.specification s).sample R bits
      rw [ht]
      simp only [WordChoiceTree.sample]
    | ask a b hb hab upper lower =>
      have ht : m.specification s = WordChoiceTree.fork a b hb hab (m.specification upper) (m.specification lower) := by
        conv_lhs => unfold specification
        rw [hs]
      change m.runCursor R (.coin a b hb hab upper lower) bits = (m.specification s).sample R bits
      rw [ht]
      exact m.runCursor_refines R (.coin a b hb hab upper lower) bits
  | coin a b hb hab upper lower =>
    conv_lhs => unfold runCursor
    conv_rhs => rw [cursorSpecification]; unfold WordChoiceTree.sample
    by_cases ha0 : a = 0
    · simp only [ha0, ite_true]
      exact m.runCursor_refines R (.state lower) bits
    by_cases hba : b ≤ a
    · simp only [ha0, hba, ite_false, ite_true]
      exact m.runCursor_refines R (.state upper) bits
    simp only [ha0, hba, ite_false]
    cases R with
    | zero => rfl
    | succ r =>
      dsimp only
      by_cases hd : bits 0 = denominatorDigit a b
      · simp only [hd, ite_true]
        exact congrArg (fun result : Option α × ℕ => (result.1, result.2 + 1))
          (m.runCursor_refines r (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (Fin.tail bits))
      · simp only [hd, ite_false]
        by_cases hbit : bits 0 = true
        · simp only [hbit, ite_true]
          exact congrArg (fun result : Option α × ℕ => (result.1, result.2 + 1))
            (m.runCursor_refines r (.state lower) (Fin.tail bits))
        · simp only [hbit]
          exact congrArg (fun result : Option α × ℕ => (result.1, result.2 + 1))
            (m.runCursor_refines r (.state upper) (Fin.tail bits))
termination_by (R, m.cursorRank cursor)
decreasing_by
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    omega
  all_goals omega

theorem run_refines {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (bits : Fin R → Bool) :
    m.run R s bits = (m.specification s).sample R bits := by
  rw [m.run_eq_numeric, runNumeric, m.runCursorIndexed_zero]
  exact m.runCursor_refines R (.state s) bits

theorem run_bits_le {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (bits : Fin R → Bool) :
    (m.run R s bits).2 ≤ R := by
  rw [m.run_refines]
  exact (m.specification s).sample_bits_le R bits

end Blotto.WordStateMachine
