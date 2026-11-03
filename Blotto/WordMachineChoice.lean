import Blotto.WordMachineFallback
import Blotto.ProbabilityWords

/-! One native word coin chooses between two state-machine continuations.
The same runtime cap is retained through the root and the selected branch. -/

namespace Blotto

theorem WordChoiceTree.forLeaves_mono {α : Type*} (T : WordChoiceTree α) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (ht : T.decode.ForLeaves P) : T.decode.ForLeaves Q := by
  induction T with
  | leaf x => exact h x ht
  | fork a b hb hab upper lower hu hl => exact ⟨hu ht.1, hl ht.2⟩

inductive BinaryState (S T : Type*) where
  | start
  | upper (state : S)
  | lower (state : T)

def binaryTransition {S T α : Type*} (w : ProbabilityWords) (a : WordStateMachine S α) (b : WordStateMachine T α)
    (sa : S) (sb : T) : BinaryState S T → WordTransition (BinaryState S T) α
  | .start => .ask w.numerator w.denominator w.denominator_pos w.normalized (.upper sa) (.lower sb)
  | .upper s => (a.step s).mapState .upper
  | .lower s => (b.step s).mapState .lower

def binaryRank {S T α : Type*} (a : WordStateMachine S α) (b : WordStateMachine T α) (sa : S) (sb : T) : BinaryState S T → ℕ
  | .start => 1 + max (a.rank sa) (b.rank sb)
  | .upper s => a.rank s
  | .lower s => b.rank s

def binaryMachine {S T α : Type*} (w : ProbabilityWords) (a : WordStateMachine S α) (b : WordStateMachine T α)
    (sa : S) (sb : T) : WordStateMachine (BinaryState S T) α where
  step := binaryTransition w a b sa sb
  rank := binaryRank a b sa sb
  progress := by
    intro state
    cases state with
    | start =>
      change a.rank sa < 1 + max (a.rank sa) (b.rank sb) ∧ b.rank sb < 1 + max (a.rank sa) (b.rank sb)
      omega
    | upper s =>
      apply WordTransition.mapState_progress
      exact a.progress s
    | lower s =>
      apply WordTransition.mapState_progress
      exact b.progress s

theorem binaryMachine_step {S T α : Type*} (w : ProbabilityWords) (a : WordStateMachine S α) (b : WordStateMachine T α)
    (sa : S) (sb : T) (state : BinaryState S T) :
    (binaryMachine w a b sa sb).step state = binaryTransition w a b sa sb state := rfl

theorem binaryMachine_upper_specification {S T α : Type*} (w : ProbabilityWords) (a : WordStateMachine S α) (b : WordStateMachine T α)
    (sa : S) (sb : T) (s : S) :
    (binaryMachine w a b sa sb).specification (.upper s) = a.specification s := by
  have hAll : ∀ n, ∀ s : S, a.rank s = n → (binaryMachine w a b sa sb).specification (.upper s) = a.specification s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      cases hs : a.step s with
      | done x =>
        have ht : (binaryMachine w a b sa sb).step (.upper s) = .done x := by
          rw [binaryMachine_step]
          simp only [binaryTransition, hs, WordTransition.mapState]
        rw [WordStateMachine.specification_of_done _ _ _ ht, a.specification_of_done _ _ hs]
      | ask u d hd hud upper lower =>
        have hp := a.progress s
        rw [hs] at hp
        have ht : (binaryMachine w a b sa sb).step (.upper s) = .ask u d hd hud (.upper upper) (.upper lower) := by
          rw [binaryMachine_step]
          simp only [binaryTransition, hs, WordTransition.mapState]
        rw [WordStateMachine.specification_of_ask _ _ _ _ _ _ _ _ ht, a.specification_of_ask _ _ _ _ _ _ _ hs]
        rw [ih (a.rank upper) (by omega) upper rfl, ih (a.rank lower) (by omega) lower rfl]
  exact hAll (a.rank s) s rfl

theorem binaryMachine_lower_specification {S T α : Type*} (w : ProbabilityWords) (a : WordStateMachine S α) (b : WordStateMachine T α)
    (sa : S) (sb : T) (s : T) :
    (binaryMachine w a b sa sb).specification (.lower s) = b.specification s := by
  have hAll : ∀ n, ∀ s : T, b.rank s = n → (binaryMachine w a b sa sb).specification (.lower s) = b.specification s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      cases hs : b.step s with
      | done x =>
        have ht : (binaryMachine w a b sa sb).step (.lower s) = .done x := by
          rw [binaryMachine_step]
          simp only [binaryTransition, hs, WordTransition.mapState]
        rw [WordStateMachine.specification_of_done _ _ _ ht, b.specification_of_done _ _ hs]
      | ask u d hd hud upper lower =>
        have hp := b.progress s
        rw [hs] at hp
        have ht : (binaryMachine w a b sa sb).step (.lower s) = .ask u d hd hud (.lower upper) (.lower lower) := by
          rw [binaryMachine_step]
          simp only [binaryTransition, hs, WordTransition.mapState]
        rw [WordStateMachine.specification_of_ask _ _ _ _ _ _ _ _ ht, b.specification_of_ask _ _ _ _ _ _ _ hs]
        rw [ih (b.rank upper) (by omega) upper rfl, ih (b.rank lower) (by omega) lower rfl]
  exact hAll (b.rank s) s rfl

theorem binaryMachine_specification {S T α : Type*} (w : ProbabilityWords) (a : WordStateMachine S α) (b : WordStateMachine T α)
    (sa : S) (sb : T) : (binaryMachine w a b sa sb).specification .start =
      .fork w.numerator w.denominator w.denominator_pos w.normalized (a.specification sa) (b.specification sb) := by
  rw [WordStateMachine.specification_of_ask _ _ _ _ _ _ _ _ (show (binaryMachine w a b sa sb).step .start = _ from rfl),
    binaryMachine_upper_specification, binaryMachine_lower_specification]

theorem binaryMachine_mean {S T α : Type*} (w : ProbabilityWords) (a : WordStateMachine S α) (b : WordStateMachine T α)
    (sa : S) (sb : T) (f : α → ℝ) :
    ((binaryMachine w a b sa sb).specification .start).decode.mean f =
      (w.rational : ℝ) * (a.specification sa).decode.mean f +
        (1 - (w.rational : ℝ)) * (b.specification sb).decode.mean f := by
  rw [binaryMachine_specification]
  rfl

end Blotto
