import Blotto.RealStateMachineRefinement
import Blotto.RealStateMachineCounts
import Blotto.RealRoundingSource
import Blotto.ArrayResourceRounding
import Blotto.RealPairProgram

/-! Real array control defers the two writes until after branch selection.
The updated array is shared between its resource and retained-pair fields;
no discarded branch update or repeated pair update is performed. Physical
reference-count/ownership costs remain a separate explicit contract. -/

namespace Blotto
open scoped Classical

namespace ArrayResourceState

noncomputable def realUpdate {n : ℕ} {L : Allocation n} (s : ArrayResourceState L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) (z : ℝ) : ArrayResourceState L :=
  let nextResource := s.resource.updatePair a b z
  { resource := nextResource
    active := retainedPair L nextResource.allocation a b ++ tail
    nodup := by
      rw [s.resource.allocation_updatePair]
      exact (s.view.update a b tail he z).nodup
    membership := by
      rw [s.resource.allocation_updatePair]
      exact (s.view.update a b tail he z).membership }

theorem realUpdate_eq_update {n : ℕ} {L : Allocation n} (s : ArrayResourceState L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) (z : ℝ) :
    s.realUpdate a b tail he z = s.update a b tail he z := rfl

theorem realUpdate_view {n : ℕ} {L : Allocation n} (s : ArrayResourceState L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) (z : ℝ) :
    (s.realUpdate a b tail he z).view = s.view.update a b tail he z := by
  rw [s.realUpdate_eq_update, s.update_view]

end ArrayResourceState

inductive RealArrayCursor {n : ℕ} (L : Allocation n) where
  | ready (fuel : ℕ) (data : ArrayResourceState L)
  | pending (fuel : ℕ) (data : ArrayResourceState L) (a b : Fin n) (tail : List (Fin n))
      (headPair : data.active = a :: b :: tail) (value : ℝ)

def RealArrayCursor.fuel {n : ℕ} {L : Allocation n} : RealArrayCursor L → ℕ
  | .ready fuel _ => fuel
  | .pending fuel _ _ _ _ _ _ => fuel

noncomputable def realArrayReadyStepReference {n : ℕ} {L : Allocation n} :
    ℕ → ArrayResourceState L → RealTransition (RealArrayCursor L) (Allocation n)
  | 0, s => .done s.resource.allocation
  | fuel + 1, s =>
    match he : s.active with
    | [] => .done s.resource.allocation
    | [_] => .done s.resource.allocation
    | a :: b :: tail =>
      let hp := s.view.selected_fractional he
      let p := resourcePair L s.resource.allocation a b hp.1 hp.2
      .ask p.probability ⟨p.probability_pos.le, p.probability_lt_one.le⟩
        (.pending fuel s a b tail he p.upper) (.pending fuel s a b tail he p.lower)

noncomputable def realArrayReadyStep {n : ℕ} {L : Allocation n} :
    ℕ → ArrayResourceState L → RealTransition (RealArrayCursor L) (Allocation n)
  | 0, s => .done s.resource.allocation
  | fuel + 1, s =>
    match he : s.active with
    | [] => .done s.resource.allocation
    | [_] => .done s.resource.allocation
    | a :: b :: tail =>
      let hp := s.view.selected_fractional he
      let p := resourcePair L s.resource.allocation a b hp.1 hp.2
      let registers := RealPairProgram.run p
      .ask (registers.getD 11 0)
        (by rw [RealPairProgram.run_probability]; exact ⟨p.probability_pos.le, p.probability_lt_one.le⟩)
        (.pending fuel s a b tail he (registers.getD 8 0))
        (.pending fuel s a b tail he (registers.getD 7 0))

theorem realArrayReadyStep_refines {n : ℕ} {L : Allocation n} (fuel : ℕ) (s : ArrayResourceState L) :
    realArrayReadyStep fuel s = realArrayReadyStepReference fuel s := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases s with
    | mk resource active nodup membership =>
      cases active with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => rfl
        | cons b tail =>
          simp only [realArrayReadyStep, realArrayReadyStepReference,
            RealPairProgram.run_probability, RealPairProgram.run_upper, RealPairProgram.run_lower]

noncomputable def realArrayStep {n : ℕ} {L : Allocation n} :
    RealArrayCursor L → RealTransition (RealArrayCursor L) (Allocation n)
  | .ready fuel s => realArrayReadyStep fuel s
  | .pending fuel s a b tail he z => realArrayReadyStep fuel (s.realUpdate a b tail he z)

theorem realArrayReadyStep_progress {n : ℕ} {L : Allocation n} (fuel : ℕ) (s : ArrayResourceState L) :
    match realArrayReadyStep fuel s with
    | .done _ => True
    | .ask _ _ upper lower => upper.fuel < fuel ∧ lower.fuel < fuel := by
  cases fuel with
  | zero => trivial
  | succ fuel =>
    cases s with
    | mk resource active nodup membership =>
      cases active with
      | nil => trivial
      | cons a rest =>
        cases rest with
        | nil => trivial
        | cons b tail =>
          change fuel < fuel + 1 ∧ fuel < fuel + 1
          omega

noncomputable def realActiveArrayMachine {n : ℕ} (L : Allocation n) :
    RealStateMachine (RealArrayCursor L) (Allocation n) where
  step := realArrayStep
  rank := RealArrayCursor.fuel
  progress := by
    intro cursor
    cases cursor with
    | ready fuel s =>
      have h := realArrayReadyStep_progress fuel s
      unfold realArrayStep
      simp only [RealArrayCursor.fuel]
      cases ht : realArrayReadyStep fuel s with
      | done value => trivial
      | ask p hp upper lower =>
        rw [ht] at h
        exact h
    | pending fuel s a b tail he z =>
      have h := realArrayReadyStep_progress fuel (s.realUpdate a b tail he z)
      unfold realArrayStep
      simp only [RealArrayCursor.fuel]
      cases ht : realArrayReadyStep fuel (s.realUpdate a b tail he z) with
      | done value => trivial
      | ask p hp upper lower =>
        rw [ht] at h
        exact h

end Blotto
