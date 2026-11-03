import Blotto.NativeAdaptiveBitHistory
import Blotto.FiniteKernelHistory

/-! A deterministic observation encoding preserves adaptive kernel execution
when next laws agree at each encoded history. The map may identify duplicate
labels. This bridge requires the concrete state/next-law refinement separately;
it does not assume that every rational row has a unique original label. -/

namespace Blotto
namespace BoundedExpectationKernel

theorem historyRun_simulation {α β : Type*} (source : List α → BoundedExpectationKernel α)
    (target : List β → BoundedExpectationKernel β) (encode : α → β)
    (hStep : ∀ history test, (source history).mean (fun x => test (encode x)) =
      (target (history.map encode)).mean test) (T : ℕ) (history : List α) (test : List β → ℝ) :
    (historyRun source T history).mean (fun h => test (h.map encode)) =
      (historyRun target T (history.map encode)).mean test := by
  induction T generalizing history with
  | zero => rfl
  | succ T ih =>
    change (source history).mean (fun x =>
      (historyRun source T (x :: history)).mean (fun h => test (h.map encode))) = _
    simp_rw [ih, List.map_cons]
    rw [hStep history (fun y => (historyRun target T (y :: history.map encode)).mean test)]
    rfl

end BoundedExpectationKernel

-- Encoded finite histories are exactly the old finite probability sum.
theorem finiteHistory_encoded_mean {a : ℕ} {β : Type*}
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ h x, 0 ≤ transition h x) (hs : ∀ h, ∑ x, transition h x = 1)
    (ideal : List β → BoundedExpectationKernel β) (encode : Fin a → β)
    (hStep : ∀ history test, (finiteTransitionKernel transition hp hs history).mean (fun x => test (encode x)) =
      (ideal (history.map encode)).mean test) (T : ℕ) (test : List β → ℝ) :
    (BoundedExpectationKernel.historyRun ideal T []).mean test =
      SparseMW.historyMean transition T (fun h => test (h.map encode)) := by
  have he := BoundedExpectationKernel.historyRun_simulation (finiteTransitionKernel transition hp hs)
    ideal encode hStep T [] test
  have hf := historyEvolution_finite_mean transition hp hs T (fun h => test (h.map encode))
  rw [BoundedExpectationKernel.historyEvolution_run_mean] at hf
  exact he.symm.trans hf

end Blotto
