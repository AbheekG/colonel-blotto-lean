import Blotto.RationalActiveResources
import Blotto.WordMachineLaw
import Blotto.RationalPairProgram

/-! The concrete PRG resource-rounding control flow over native rational
arrays. Successors defer their update, so only the selected branch performs
the two writes. The rank counts remaining fractional pairs; transition ranking
is erased from execution. This phase returns a terminal resource state. -/

namespace Blotto

inductive RationalResourceCursor {n : ℕ} (L : Fin n → ℚ) where
  | ready (state : RationalActiveResources L)
  | selected (state : RationalActiveResources L) (a b : Fin n) (tail : List (Fin n))
      (head_pair : state.active = a :: b :: tail) (value : ℚ)

namespace RationalResourceCursor

def materialize {n : ℕ} {L : Fin n → ℚ} : RationalResourceCursor L → RationalActiveResources L
  | .ready s => s
  | .selected s a b tail he z => s.update a b tail he z

end RationalResourceCursor

def rationalResourceStepReference {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L) :
    WordTransition (RationalResourceCursor L) (RationalActiveResources L) := by
  cases s with
  | mk resource active hn hm =>
    cases active with
    | nil => exact .done ⟨resource, [], hn, hm⟩
    | cons a rest =>
      cases rest with
      | nil => exact .done ⟨resource, [a], hn, hm⟩
      | cons b tail =>
        let s : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        let p := s.pair a b tail rfl
        let w := p.words
        exact .ask w.numerator w.denominator w.denominator_pos w.normalized
          (.selected s a b tail rfl p.upper) (.selected s a b tail rfl p.lower)

def rationalResourceStep {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L) :
    WordTransition (RationalResourceCursor L) (RationalActiveResources L) := by
  cases s with
  | mk resource active hn hm =>
    cases active with
    | nil => exact .done ⟨resource, [], hn, hm⟩
    | cons a rest =>
      cases rest with
      | nil => exact .done ⟨resource, [a], hn, hm⟩
      | cons b tail =>
        let s : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        let p := s.pair a b tail rfl
        let registers := RationalPairProgram.run p
        let w := RationalPairProgram.words p registers rfl
        exact .ask w.numerator w.denominator w.denominator_pos w.normalized
          (.selected s a b tail rfl (registers.getD 8 0))
          (.selected s a b tail rfl (registers.getD 7 0))

theorem rationalResourceStep_refines {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L) :
    rationalResourceStep s = rationalResourceStepReference s := by
  cases s with
  | mk resource active hn hm =>
    cases active with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b tail =>
        simp only [rationalResourceStep, rationalResourceStepReference,
          RationalPairProgram.words_eq, RationalPairProgram.run_upper, RationalPairProgram.run_lower]

def rationalResourceTransition {n : ℕ} {L : Fin n → ℚ} (cursor : RationalResourceCursor L) :
    WordTransition (RationalResourceCursor L) (RationalActiveResources L) := rationalResourceStep cursor.materialize

theorem rationalResourceStep_progress {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L) :
    match rationalResourceStep s with
    | .done _ => True
    | .ask _ _ _ _ upper lower => upper.materialize.active.length - 1 < s.active.length - 1 ∧
        lower.materialize.active.length - 1 < s.active.length - 1 := by
  rw [rationalResourceStep_refines]
  cases s with
  | mk resource active hn hm =>
    cases active with
    | nil => trivial
    | cons a rest =>
      cases rest with
      | nil => trivial
      | cons b tail =>
        let s : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        let p := s.pair a b tail rfl
        have hu := s.update_length_lt a b tail rfl (Or.inr rfl : p.upper = p.lower ∨ p.upper = p.upper)
        have hl := s.update_length_lt a b tail rfl (Or.inl rfl : p.lower = p.lower ∨ p.lower = p.upper)
        change (s.update a b tail rfl p.upper).active.length - 1 < s.active.length - 1 ∧
          (s.update a b tail rfl p.lower).active.length - 1 < s.active.length - 1
        have hlen : 2 ≤ s.active.length := by simp [s]
        constructor <;> omega

def rationalResourceMachine {n : ℕ} (L : Fin n → ℚ) :
    WordStateMachine (RationalResourceCursor L) (RationalActiveResources L) where
  step := rationalResourceTransition
  rank := fun cursor => cursor.materialize.active.length - 1
  progress := by
    intro cursor
    have hp := rationalResourceStep_progress cursor.materialize
    unfold rationalResourceTransition
    cases hs : rationalResourceStep cursor.materialize with
    | done value => trivial
    | ask a b hb hab upper lower =>
      rw [hs] at hp
      exact hp

theorem rationalResourceStep_terminal {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L) :
    match rationalResourceStep s with
    | .done value => value.active.length ≤ 1
    | .ask _ _ _ _ _ _ => True := by
  rw [rationalResourceStep_refines]
  cases s with
  | mk resource active hn hm =>
    cases active with
    | nil => simp [rationalResourceStepReference]
    | cons a rest =>
      cases rest with
      | nil => simp [rationalResourceStepReference]
      | cons b tail => trivial

theorem rationalResourceMachine_initial_rank {n : ℕ} (L r : Fin n → ℚ) :
    (rationalResourceMachine L).rank (.ready (RationalActiveResources.initial L r)) ≤ n - 1 := by
  exact Nat.sub_le_sub_right (RationalActiveResources.initial_length_le L r) 1

theorem rationalResourceMachine_terminal {n : ℕ} (L : Fin n → ℚ) (cursor : RationalResourceCursor L)
    (R : ℕ) (bits : Fin R → Bool) {result : RationalActiveResources L}
    (hr : ((rationalResourceMachine L).run R cursor bits).1 = some result) : result.active.length ≤ 1 := by
  apply (rationalResourceMachine L).accepted_invariant R cursor bits (fun _ => True)
    (fun s => s.active.length ≤ 1) _ trivial hr
  intro c _
  have hp := rationalResourceStep_terminal c.materialize
  unfold rationalResourceMachine rationalResourceTransition
  dsimp only
  cases hs : rationalResourceStep c.materialize with
  | done value => rw [hs] at hp; exact hp
  | ask a b hb hab upper lower => trivial

theorem rationalResourceMachine_failure_probability {n : ℕ} (L r : Fin n → ℚ) (K : ℕ) :
    (fairBitLaw (3 * (n - 1 + K)) : MeasureTheory.Measure (Fin (3 * (n - 1 + K)) → Bool)).real
      {bits | ((rationalResourceMachine L).run (3 * (n - 1 + K)) (.ready (RationalActiveResources.initial L r)) bits).1 = none} ≤
      1 / (2 : ℝ) ^ K := by
  exact (rationalResourceMachine L).failure_probability_precision (n - 1) K
    (.ready (RationalActiveResources.initial L r)) (rationalResourceMachine_initial_rank L r)

end Blotto
