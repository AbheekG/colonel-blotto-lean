import Blotto.LottoResourceSystem
import Blotto.TerminalLottoPaths

/-! Global output paths: follow resource-rounding choices, then sample the
grouped terminal descriptor. Every valid pair of unit parameters is safe. -/

namespace Blotto
open scoped BigOperators

namespace LottoResourceSystem

noncomputable def point {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool)
    (useUniform : Bool) (innerChoice : ℕ → Bool) (useFamily : Bool) (r t : ℝ)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) : Allocation n := by
  classical
  let resource := i.tree.traceLeaf roundChoice
  exact if hr : i.Valid resource then (i.terminal resource hr).point useUniform innerChoice useFamily r t index edge residualEdge
    else 0

theorem point_fullBudget {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool)
    (useUniform : Bool) (innerChoice : ℕ → Bool) (useFamily : Bool) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.B (i.point roundChoice useUniform innerChoice useFamily r t index edge residualEdge) := by
  classical
  have hv := i.tree.trace_forLeaves i.Valid i.tree_valid roundChoice
  rw [point, dite_eq_left hv]
  exact (i.terminal _ hv).point_fullBudget useUniform innerChoice useFamily hr ht index edge residualEdge

noncomputable def runState {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool) :
    ActiveResourceList i.length × ℕ :=
  runActiveResources (n - 1) (ActiveResourceList.initial i.length i.initial) roundChoice

theorem runState_resource {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool) :
    (i.runState roundChoice).1.resource = i.tree.traceLeaf roundChoice :=
  runActiveResources_eq_trace _ _ _

theorem runState_updates {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool) :
    (i.runState roundChoice).2 ≤ n - 1 := runActiveResources_updates _ _ _

theorem runState_valid {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool) :
    i.Valid (i.runState roundChoice).1.resource := by
  rw [i.runState_resource]
  exact i.tree.trace_forLeaves i.Valid i.tree_valid roundChoice

/-- This version evaluates only the selected resource path. -/
noncomputable def runPoint {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool)
    (useUniform : Bool) (innerChoice : ℕ → Bool) (useFamily : Bool) (r t : ℝ)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) : Allocation n :=
  (i.terminal (i.runState roundChoice).1.resource (i.runState_valid roundChoice)).point
    useUniform innerChoice useFamily r t index edge residualEdge

theorem runPoint_eq_point {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool)
    (useUniform : Bool) (innerChoice : ℕ → Bool) (useFamily : Bool) (r t : ℝ)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) :
    i.runPoint roundChoice useUniform innerChoice useFamily r t index edge residualEdge =
      i.point roundChoice useUniform innerChoice useFamily r t index edge residualEdge := by
  classical
  simp only [runPoint, point, i.runState_resource,
    dite_eq_left (i.tree.trace_forLeaves i.Valid i.tree_valid roundChoice)]

theorem runPoint_fullBudget {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool)
    (useUniform : Bool) (innerChoice : ℕ → Bool) (useFamily : Bool) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.B (i.runPoint roundChoice useUniform innerChoice useFamily r t index edge residualEdge) :=
  (i.terminal _ (i.runState_valid roundChoice)).point_fullBudget
    useUniform innerChoice useFamily hr ht index edge residualEdge

end LottoResourceSystem
end Blotto
