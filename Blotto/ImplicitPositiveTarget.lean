import Blotto.ImplicitAllocationDecoder

/-! Positive stored leaf blocks imply positive mass for every original
Cartesian label. One feasible fallback therefore derives positive conditional
target mass; no separate normalizer-positivity oracle is needed. -/

namespace Blotto.ImplicitLeafCounts.ProposalTree
open scoped BigOperators Classical

theorem trueFamily_mass_positive (tree : ProposalTree) :
    ∀ label : Fin tree.projected.real.trueSize, 0 < tree.projected.real.trueFamily.mass label := by
  induction tree with
  | leaf data guide gamma =>
    intro label
    change (0 : ℝ) < (labelMass data.blocks label.val : ℝ)
    exact_mod_cast partition_labelMass_positive data.cap data.blocks data.partition data.positive label
  | fork guide gamma left right ihL ihR =>
    intro label
    change 0 < (left.projected.real.trueFamily.product right.projected.real.trueFamily).mass label
    unfold WeightedResourceFamily.product
    exact mul_pos (ihL (finProdFinEquiv.symm label).1) (ihR (finProdFinEquiv.symm label).2)

theorem prefix_positive_of_feasible_label (tree : ProposalTree) (budget : ℚ)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)) :
    0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ) := by
  apply (tree.projected.real.trueFamily.prefix_positive_iff_exists (budget : ℝ)).mpr
  exact ⟨fallback.cast tree.projected.real_trueSize.symm, hf, tree.trueFamily_mass_positive _⟩

end Blotto.ImplicitLeafCounts.ProposalTree
