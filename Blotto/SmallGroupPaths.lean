import Blotto.SmallGroupLaws

/-! Every valid output path of the two/three-group constructors is feasible,
including component slots with zero probability. These maps alone do not
specify the random input law or computational operation counts. -/

namespace Blotto
open scoped BigOperators

namespace UniformGroupSpec

noncomputable def point {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (edge : Fin 9) (t : ℝ) : Allocation m := by
  by_cases h2 : m = 2
  · subst m; exact complementaryPairPoint i.B t
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.threeInput.point edge t

theorem point_fullBudget {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (edge : Fin 9) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) : FullBudget i.B (i.point hm edge t) := by
  rcases hm with rfl | rfl
  · change FullBudget i.B (complementaryPairPoint i.B t)
    exact complementaryPairPoint_fullBudget (le_of_lt i.B_pos) ht
  · change FullBudget i.B (i.threeInput.point edge t)
    exact i.threeInput.point_fullBudget edge ht

end UniformGroupSpec

namespace MixedGroupSpec

noncomputable def point {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (useUniform : Bool) (choice : ℕ → Bool) (useFamily : Bool) (r t : ℝ)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) : Allocation (m + 1) := by
  by_cases h2 : m = 2
  · subst m; exact i.threeInput.point edge t
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.fourInput.point useUniform choice useFamily r t index edge residualEdge

theorem point_fullBudget {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (useUniform : Bool) (choice : ℕ → Bool) (useFamily : Bool) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.B (i.point hm useUniform choice useFamily r t index edge residualEdge) := by
  rcases hm with rfl | rfl
  · change FullBudget i.B (i.threeInput.point edge t)
    exact i.threeInput.point_fullBudget edge ht
  · change FullBudget i.B (i.fourInput.point useUniform choice useFamily r t index edge residualEdge)
    exact i.fourInput.point_fullBudget useUniform choice useFamily hr ht index edge residualEdge

end MixedGroupSpec
end Blotto
