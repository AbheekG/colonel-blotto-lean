import Blotto.RationalGroupProgramHeight
import Blotto.PreparedGroupEmissionCost
import Blotto.CachedEmissionBounds

/-! Emission prices use leaves of the actual low-dimensional group controller.
The indexed cap/position is unchanged. Small-vector production and the physical
backend remain distinct from the output coordinate pass. -/

namespace Blotto.RationalUniformGroupSpec

theorem FieldsHeight.emissionWork_bound {m n : ℕ} {i : RationalUniformGroupSpec m} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3)
    {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (hCoefficients : ∀ j, RationalHeight (p.table.read j).2 s) (model : RationalCostModel)
    (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (i.program hm K scalarBits).machine.cachedEmissionWork (p.emitBitCost model) N bits
      (.state (i.program hm K scalarBits).start) pos hpos ≤
        (m + 4 * n) * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 22) := by
  let w := max s (K + 2)
  have hW : 2 ≤ expressionHeightBudget w 21 := hs.trans
    ((le_max_left s (K + 2)).trans (expressionHeightBudget_ge_input w 21))
  have hCoef := fun j => (hCoefficients j).mono
    ((le_max_left s (K + 2)).trans (expressionHeightBudget_ge_input w 21))
  apply WordStateMachine.cachedEmissionWork_leaves_bound
  apply WordChoiceTree.forLeaves_mono _ _ _ _ (h.program_leaves hs hm K scalarBits)
  intro y hy
  have hc := p.emitBitCost_bound model y (expressionHeightBudget w 21) hW hCoef hy
  simpa only [expressionHeightBudget_comp] using hc

end Blotto.RationalUniformGroupSpec
namespace Blotto.RationalMixedGroupSpec

theorem FieldsHeight.emissionWork_bound {m n : ℕ} {i : RationalMixedGroupSpec m} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3)
    {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G) (pivot : Fin n)
    (hCoefficients : ∀ j, RationalHeight (p.table.read j).2 s) (model : RationalCostModel)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (i.program hm K outerBits scalarBits).machine.cachedEmissionWork (p.emitMixedBitCost model pivot) N bits
      (.state (i.program hm K outerBits scalarBits).start) pos hpos ≤
        (m + 1 + 8 * n) * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 74) := by
  let w := max s (K + 2)
  have hW : 2 ≤ expressionHeightBudget w 72 := hs.trans
    ((le_max_left s (K + 2)).trans (expressionHeightBudget_ge_input w 72))
  have hCoef := fun j => (hCoefficients j).mono
    ((le_max_left s (K + 2)).trans (expressionHeightBudget_ge_input w 72))
  apply WordStateMachine.cachedEmissionWork_leaves_bound
  apply WordChoiceTree.forLeaves_mono _ _ _ _ (h.program_leaves hs hm K outerBits scalarBits)
  intro y hy
  have hc := p.emitMixedBitCost_bound model pivot y (expressionHeightBudget w 72) hW hCoef hy
  simpa only [expressionHeightBudget_comp] using hc

end Blotto.RationalMixedGroupSpec
