import Blotto.RealDeferredArraySource
import Blotto.RealActiveSource

/-! Deferred array execution has exactly the retained active-list value and
input count, for every buffer size and seed, including capped executions. -/

namespace Blotto

theorem realActiveArrayMachine_specification_aux {n : ℕ} {L : Allocation n} (fuel : ℕ)
    (s : ArrayResourceState L) (cursor : RealArrayCursor L)
    (hStep : (realActiveArrayMachine L).step cursor = realArrayReadyStep fuel s) :
    (realActiveArrayMachine L).specification cursor = (roundActiveResources fuel s.view).realChoice := by
  induction fuel generalizing s cursor with
  | zero =>
    rw [(realActiveArrayMachine L).specification_done cursor s.resource.allocation hStep]
    rfl
  | succ fuel ih =>
    rw [realArrayReadyStep_refines] at hStep
    cases s with
    | mk resource active nodup membership =>
      cases active with
      | nil =>
        rw [(realActiveArrayMachine L).specification_done cursor resource.allocation hStep]
        rfl
      | cons a rest =>
        cases rest with
        | nil =>
          rw [(realActiveArrayMachine L).specification_done cursor resource.allocation hStep]
          rfl
        | cons b tail =>
          let s : ArrayResourceState L := ⟨resource, a :: b :: tail, nodup, membership⟩
          let hp := s.view.selected_fractional rfl
          let p := resourcePair L s.resource.allocation a b hp.1 hp.2
          change (realActiveArrayMachine L).step cursor = .ask p.probability _
            (.pending fuel s a b tail rfl p.upper) (.pending fuel s a b tail rfl p.lower) at hStep
          rw [(realActiveArrayMachine L).specification_ask cursor p.probability _ _ _ hStep]
          rw [ih (s.realUpdate a b tail rfl p.upper) (.pending fuel s a b tail rfl p.upper) rfl,
            ih (s.realUpdate a b tail rfl p.lower) (.pending fuel s a b tail rfl p.lower) rfl,
            s.realUpdate_view a b tail rfl p.upper, s.realUpdate_view a b tail rfl p.lower]
          rfl

theorem realActiveArrayMachine_specification_ready {n : ℕ} {L : Allocation n} (fuel : ℕ) (s : ArrayResourceState L) :
    (realActiveArrayMachine L).specification (.ready fuel s) = (roundActiveResources fuel s.view).realChoice :=
  realActiveArrayMachine_specification_aux fuel s (.ready fuel s) rfl

theorem realActiveArrayMachine_specification_pending {n : ℕ} {L : Allocation n} (fuel : ℕ)
    (s : ArrayResourceState L) (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) (z : ℝ) :
    (realActiveArrayMachine L).specification (.pending fuel s a b tail he z) =
      (roundActiveResources fuel (s.realUpdate a b tail he z).view).realChoice :=
  realActiveArrayMachine_specification_aux fuel _ (.pending fuel s a b tail he z) rfl

theorem realActiveArrayMachine_run_eq_list {n : ℕ} {L : Allocation n} (fuel C : ℕ)
    (s : ArrayResourceState L) (seed : Fin C → ℝ) :
    (realActiveArrayMachine L).run C (.ready fuel s) seed =
      (realActiveResourceMachine L).run C (fuel, s.view) seed := by
  rw [RealStateMachine.run_refines, realActiveArrayMachine_specification_ready,
    RealStateMachine.run_refines, realActiveResourceMachine_specification]

end Blotto
