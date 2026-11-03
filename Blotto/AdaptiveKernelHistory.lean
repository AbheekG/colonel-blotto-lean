import Blotto.FairBitKernelBlocks

/-! Sequential kernel comparison keeps the entire realized history in state.
At every shared history the actual and ideal next-observation kernels are
compared; deterministic updates may be adaptive. Error is accumulated before
postprocessing events, rather than conditioning on a favorable history. -/

namespace Blotto
open scoped Classical
namespace BoundedExpectationKernel

noncomputable def historyRun {α : Type*} (step : List α → BoundedExpectationKernel α) :
    ℕ → List α → BoundedExpectationKernel (List α)
  | 0, history => point history
  | t + 1, history => (step history).bind (fun observation => historyRun step t (observation :: history))

theorem historyRun_close {α : Type*} (actual ideal : List α → BoundedExpectationKernel α)
    (error : ℝ) (_herror : 0 ≤ error) (hstep : ∀ history, (actual history).Close (ideal history) error)
    (T : ℕ) (history : List α) :
    (historyRun actual T history).Close (historyRun ideal T history) ((T : ℝ) * error) := by
  induction T generalizing history with
  | zero =>
    intro test _hTest
    simp [historyRun, point]
  | succ T ih =>
    have h := bind_close (actual history) (ideal history)
      (fun x => historyRun actual T (x :: history)) (fun x => historyRun ideal T (x :: history))
      error ((T : ℝ) * error) (hstep history) (fun x => ih (x :: history))
    simpa only [historyRun, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using h

theorem historyRun_event_error {α : Type*} (actual ideal : List α → BoundedExpectationKernel α)
    (error : ℝ) (herror : 0 ≤ error) (hstep : ∀ history, (actual history).Close (ideal history) error)
    (T : ℕ) (history : List α) (event : Set (List α)) :
    |(historyRun actual T history).mean (fun h => if h ∈ event then 1 else 0) -
      (historyRun ideal T history).mean (fun h => if h ∈ event then 1 else 0)| ≤ (T : ℝ) * error := by
  classical
  exact historyRun_close actual ideal error herror hstep T history
    (fun h => if h ∈ event then 1 else 0) (fun h => by split_ifs <;> norm_num)

theorem historyRun_postprocess_close {α β : Type*} (actual ideal : List α → BoundedExpectationKernel α)
    (error : ℝ) (herror : 0 ≤ error) (hstep : ∀ history, (actual history).Close (ideal history) error)
    (T : ℕ) (history : List α) (output : List α → β) :
    ((historyRun actual T history).map output).Close ((historyRun ideal T history).map output) ((T : ℝ) * error) :=
  map_close _ _ output _ (historyRun_close actual ideal error herror hstep T history)

noncomputable def historyEvolution {α : Type*} (step : List α → BoundedExpectationKernel α) :
    ℕ → BoundedExpectationKernel (List α)
  | 0 => point []
  | t + 1 => (historyEvolution step t).bind (fun h => (step h).map (fun x => x :: h))

theorem historyEvolution_close {α : Type*} (actual ideal : List α → BoundedExpectationKernel α)
    (error : ℝ) (_herror : 0 ≤ error) (hstep : ∀ h, (actual h).Close (ideal h) error) (T : ℕ) :
    (historyEvolution actual T).Close (historyEvolution ideal T) ((T : ℝ) * error) := by
  induction T with
  | zero => intro f _hf; simp [historyEvolution, point]
  | succ T ih =>
    have he := bind_close (historyEvolution actual T) (historyEvolution ideal T)
      (fun h => (actual h).map (fun x => x :: h)) (fun h => (ideal h).map (fun x => x :: h))
      ((T : ℝ) * error) error ih (fun h => map_close _ _ (fun x => x :: h) error (hstep h))
    simpa only [historyEvolution, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using he

theorem historyRun_next_mean {α : Type*} (step : List α → BoundedExpectationKernel α)
    (T : ℕ) (history : List α) (test : List α → ℝ) :
    (historyRun step T history).mean (fun h => (step h).mean (fun x => test (x :: h))) =
      (historyRun step (T + 1) history).mean test := by
  induction T generalizing history with
  | zero => rfl
  | succ T ih =>
    change (step history).mean (fun x =>
      (historyRun step T (x :: history)).mean (fun h => (step h).mean (fun y => test (y :: h)))) = _
    simp_rw [ih]
    rfl

theorem historyEvolution_run_mean {α : Type*} (step : List α → BoundedExpectationKernel α)
    (T : ℕ) (test : List α → ℝ) :
    (historyEvolution step T).mean test = (historyRun step T []).mean test := by
  induction T generalizing test with
  | zero => rfl
  | succ T ih =>
    change (historyEvolution step T).mean (fun h => (step h).mean (fun x => test (x :: h))) = _
    rw [ih, historyRun_next_mean]

theorem historyRun_close_before {α : Type*} (actual ideal : List α → BoundedExpectationKernel α)
    (error : ℝ) (_herror : 0 ≤ error) (limit : ℕ)
    (hstep : ∀ history, history.length < limit → (actual history).Close (ideal history) error)
    (T : ℕ) (history : List α) (hLength : T + history.length ≤ limit) :
    (historyRun actual T history).Close (historyRun ideal T history) ((T : ℝ) * error) := by
  induction T generalizing history with
  | zero => intro f _hf; simp [historyRun, point]
  | succ T ih =>
    have he := bind_close (actual history) (ideal history)
      (fun x => historyRun actual T (x :: history)) (fun x => historyRun ideal T (x :: history))
      error ((T : ℝ) * error) (hstep history (by omega))
      (fun x => ih (x :: history) (by simp only [List.length_cons]; omega))
    simpa only [historyRun, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using he

end BoundedExpectationKernel
end Blotto
