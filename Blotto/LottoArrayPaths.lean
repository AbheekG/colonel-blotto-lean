import Blotto.ArrayResourceRounding
import Blotto.LottoResourcePaths

/-! The array-based resource path feeds the same terminal allocation
descriptor as the abstract law construction, with exact hard-budget output. -/

namespace Blotto

namespace LottoResourceSystem

noncomputable def runArrayState {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool) :
    ArrayResourceState i.length × ℕ :=
  runArrayResources (n - 1) (ArrayResourceState.initial i.length i.initial) roundChoice

theorem runArrayState_resource {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool) :
    (i.runArrayState roundChoice).1.resource.allocation = i.tree.traceLeaf roundChoice := by
  change (runArrayResources (n - 1) (ArrayResourceState.initial i.length i.initial) roundChoice).1.resource.allocation = _
  rw [runArrayResources_eq_trace, ArrayResourceState.initial_view]
  rfl

theorem runArrayState_updates {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool) :
    (i.runArrayState roundChoice).2 ≤ n - 1 := runArrayResources_updates _ _ _

theorem runArrayState_valid {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool) :
    i.Valid (i.runArrayState roundChoice).1.resource.allocation := by
  rw [i.runArrayState_resource]
  exact i.tree.trace_forLeaves i.Valid i.tree_valid roundChoice

noncomputable def runArrayPoint {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool)
    (useUniform : Bool) (innerChoice : ℕ → Bool) (useFamily : Bool) (r t : ℝ)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) : Allocation n :=
  (i.terminal (i.runArrayState roundChoice).1.resource.allocation (i.runArrayState_valid roundChoice)).point
    useUniform innerChoice useFamily r t index edge residualEdge

theorem runArrayPoint_eq_point {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool)
    (useUniform : Bool) (innerChoice : ℕ → Bool) (useFamily : Bool) (r t : ℝ)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) :
    i.runArrayPoint roundChoice useUniform innerChoice useFamily r t index edge residualEdge =
      i.point roundChoice useUniform innerChoice useFamily r t index edge residualEdge := by
  classical
  simp only [runArrayPoint, point, i.runArrayState_resource,
    dite_eq_left (i.tree.trace_forLeaves i.Valid i.tree_valid roundChoice)]

theorem runArrayPoint_fullBudget {n : ℕ} (i : LottoResourceSystem n) (roundChoice : ℕ → Bool)
    (useUniform : Bool) (innerChoice : ℕ → Bool) (useFamily : Bool) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.B (i.runArrayPoint roundChoice useUniform innerChoice useFamily r t index edge residualEdge) :=
  (i.terminal _ (i.runArrayState_valid roundChoice)).point_fullBudget
    useUniform innerChoice useFamily hr ht index edge residualEdge

end LottoResourceSystem
end Blotto
