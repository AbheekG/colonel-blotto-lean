import Blotto.RationalRecursiveProposalKernel

/-! Normalized kernels evaluate exact positive conditional weights. At zero
mass their deterministic failure is explicit; no unspecified conditional law
is used. These identities prepare the join to the recursive Q record formula. -/

namespace Blotto
open scoped BigOperators Classical

theorem totalNormalizedKernel_mean {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i)
    (ht : 0 < ∑ i, weights i) (f : Option (Fin r) → ℝ) :
    (totalNormalizedKernel weights hn).mean f =
      ∑ i, ((weights i / ∑ j, weights j : ℚ) : ℝ) * f (some i) := by
  unfold totalNormalizedKernel
  rw [dite_eq_left ht]
  rfl

theorem totalNormalizedKernel_zero_mean {r : ℕ} (weights : Fin r → ℚ) (hn : ∀ i, 0 ≤ weights i)
    (ht : ¬ 0 < ∑ i, weights i) (f : Option (Fin r) → ℝ) :
    (totalNormalizedKernel weights hn).mean f = f none := by
  unfold totalNormalizedKernel
  rw [dite_eq_right ht]
  rfl

namespace RationalWeightedGuideTree

theorem leafKernel_mean {n p : ℕ} (family : RationalWeightedFamily n)
    (guide : RationalWeightedFamily p) (gamma B : ℚ) (K : ℕ)
    (hm : 0 < family.prefixMass B) (f : Option (Fin n) → ℝ) :
    ((RationalWeightedGuideTree.leaf family guide gamma).proposalKernel false B K).mean f =
      ∑ i, (((RationalWeightedGuideTree.leaf family guide gamma).probability B i : ℚ) : ℝ) * f (some i) := by
  have ht : 0 < ∑ i, leafWeights family B i := hm
  change (totalNormalizedKernel (leafWeights family B) _).mean f = _
  rw [totalNormalizedKernel_mean _ _ ht]
  apply @Fintype.sum_equiv (Fin n) (Fin n) ℝ (Fin.fintype n)
    (RationalWeightedGuideTree.recordFintype (.leaf family guide gamma)) _ (Equiv.refl (Fin n))
  intro i
  simp only [Equiv.refl_apply]
  change (((if family.resource i ≤ B then family.mass i else 0) / family.prefixMass B : ℚ) : ℝ) * f (some i) =
    ((if family.resource i ≤ B then family.mass i / family.prefixMass B else 0 : ℚ) : ℝ) * f (some i)
  by_cases hr : family.resource i ≤ B
  · simp only [hr, ite_true, RationalWeightedFamily.prefixMass]
  · simp only [hr, ite_false, zero_div, Rat.cast_zero, zero_mul]

end RationalWeightedGuideTree
end Blotto
