import Blotto.WordMachineSerial

/-! The serial controller's specification is the source tree with each leaf
replaced by its selected continuation. This identity connects the concrete
single-cap runtime to the sequential ideal law, without runtime tree expansion. -/

namespace Blotto.WordStateMachine

theorem specification_of_done {S α : Type*} (m : WordStateMachine S α) (s : S) (x : α)
    (h : m.step s = .done x) : m.specification s = .leaf x := by
  conv_lhs => unfold specification
  rw [h]

theorem specification_of_ask {S α : Type*} (m : WordStateMachine S α) (s : S)
    (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (upper lower : S) (h : m.step s = .ask a b hb hab upper lower) :
    m.specification s = .fork a b hb hab (m.specification upper) (m.specification lower) := by
  conv_lhs => unfold specification
  rw [h]

theorem specification_eq_of_step {S α : Type*} (m : WordStateMachine S α) (s t : S)
    (h : m.step s = m.step t) : m.specification s = m.specification t := by
  conv_lhs => unfold specification
  conv_rhs => unfold specification
  rw [h]

theorem serial_step {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (s : SerialState S α T) :
    (m.serial next start C hC).step s = serialTransition m next start s := rfl

theorem serial_continuation_specification {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (a : α) (s : T a) :
    (m.serial next start C hC).specification (.continuation a s) = (next a).specification s := by
  have hAll : ∀ n, ∀ s : T a, (next a).rank s = n →
      (m.serial next start C hC).specification (.continuation a s) = (next a).specification s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      cases hs : (next a).step s with
      | done x =>
        have ht : (m.serial next start C hC).step (.continuation a s) = .done x := by
          rw [m.serial_step]
          simp only [serialTransition, hs, WordTransition.mapState]
        rw [specification_of_done _ _ _ ht, specification_of_done _ _ _ hs]
      | ask u d hd hud upper lower =>
        have hp := (next a).progress s
        rw [hs] at hp
        have ht : (m.serial next start C hC).step (.continuation a s) =
            .ask u d hd hud (.continuation a upper) (.continuation a lower) := by
          rw [m.serial_step]
          simp only [serialTransition, hs, WordTransition.mapState]
        rw [specification_of_ask _ _ _ _ _ _ _ _ ht, specification_of_ask _ _ _ _ _ _ _ _ hs]
        rw [ih ((next a).rank upper) (by omega) upper rfl, ih ((next a).rank lower) (by omega) lower rfl]
  exact hAll ((next a).rank s) s rfl

theorem serial_source_specification {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (s : S) :
    (m.serial next start C hC).specification (.source s) =
      (m.specification s).bind (fun a => (next a).specification (start a)) := by
  have hAll : ∀ n, ∀ s : S, m.rank s = n →
      (m.serial next start C hC).specification (.source s) =
        (m.specification s).bind (fun a => (next a).specification (start a)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      cases hs : m.step s with
      | done a =>
        have ht : (m.serial next start C hC).step (.source s) =
            (m.serial next start C hC).step (.continuation a (start a)) := by
          rw [m.serial_step, m.serial_step]
          simp only [serialTransition, hs]
        rw [specification_eq_of_step _ _ _ ht, m.serial_continuation_specification]
        rw [specification_of_done _ _ _ hs]
        rfl
      | ask u d hd hud upper lower =>
        have hp := m.progress s
        rw [hs] at hp
        have ht : (m.serial next start C hC).step (.source s) = .ask u d hd hud (.source upper) (.source lower) := by
          rw [m.serial_step]
          simp only [serialTransition, hs]
        rw [specification_of_ask _ _ _ _ _ _ _ _ ht, specification_of_ask _ _ _ _ _ _ _ _ hs]
        simp only [WordChoiceTree.bind]
        rw [ih (m.rank upper) (by omega) upper rfl, ih (m.rank lower) (by omega) lower rfl]
  exact hAll (m.rank s) s rfl

theorem serial_mean {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (s : S) (f : β → ℝ) :
    ((m.serial next start C hC).specification (.source s)).decode.mean f =
      (m.specification s).decode.mean (fun a => ((next a).specification (start a)).decode.mean f) := by
  rw [m.serial_source_specification, WordChoiceTree.bind_mean]

end Blotto.WordStateMachine
