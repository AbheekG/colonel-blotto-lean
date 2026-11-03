import Blotto.RealRoundingSource
import Blotto.ActiveResourceRounding

/-! Exact real control selects only the maintained head pair and reuses its
tail. Functional vector updates retain their existing mathematical meaning;
array ownership and primitive costs are separate refinement obligations. -/

namespace Blotto
open scoped Classical

noncomputable def realActiveResourceStep {n : ℕ} {L : Allocation n} :
    (ℕ × ActiveResourceList L) → RealTransition (ℕ × ActiveResourceList L) (Allocation n)
  | (0, s) => .done s.resource
  | (fuel + 1, s) =>
    match he : s.active with
    | [] => .done s.resource
    | [_] => .done s.resource
    | a :: b :: tail =>
      let hp := s.selected_fractional he
      let p := resourcePair L s.resource a b hp.1 hp.2
      .ask p.probability ⟨p.probability_pos.le, p.probability_lt_one.le⟩
        (fuel, s.update a b tail he p.upper) (fuel, s.update a b tail he p.lower)

noncomputable def realActiveResourceMachine {n : ℕ} (L : Allocation n) :
    RealStateMachine (ℕ × ActiveResourceList L) (Allocation n) where
  step := realActiveResourceStep
  rank := Prod.fst
  progress := by
    rintro ⟨fuel, s⟩
    cases fuel with
    | zero => trivial
    | succ fuel =>
      cases s with
      | mk resource active nodup membership =>
        cases active with
        | nil => simp [realActiveResourceStep]
        | cons a rest =>
          cases rest with
          | nil => simp [realActiveResourceStep]
          | cons b tail => simp [realActiveResourceStep]

theorem realActiveResourceMachine_specification {n : ℕ} {L : Allocation n}
    (fuel : ℕ) (s : ActiveResourceList L) :
    (realActiveResourceMachine L).specification (fuel, s) = (roundActiveResources fuel s).realChoice := by
  induction fuel generalizing s with
  | zero =>
    rw [(realActiveResourceMachine L).specification_done _ s.resource rfl]
    rfl
  | succ fuel ih =>
    cases s with
    | mk resource active nodup membership =>
      cases active with
      | nil =>
        rw [(realActiveResourceMachine L).specification_done _ resource rfl]
        rfl
      | cons a rest =>
        cases rest with
        | nil =>
          rw [(realActiveResourceMachine L).specification_done _ resource rfl]
          rfl
        | cons b tail =>
          let s : ActiveResourceList L := ⟨resource, a :: b :: tail, nodup, membership⟩
          let hp := s.selected_fractional rfl
          let p := resourcePair L s.resource a b hp.1 hp.2
          conv_lhs => unfold RealStateMachine.specification
          change RealChoiceTree.fork p.probability _
            ((realActiveResourceMachine L).specification (fuel, s.update a b tail rfl p.upper))
            ((realActiveResourceMachine L).specification (fuel, s.update a b tail rfl p.lower)) = _
          rw [ih, ih]
          rfl

end Blotto
