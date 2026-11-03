import Blotto.ConstructedImplicitGuideBounds

/-! Actual constructed guide sizes supply all structural seed-budget caps.
The range bound is a rational input certificate for the original stored leaf
weights, not a guide-cardinality oracle. Its rounded learner/input instantiation
and full binary preparation costs remain separate. -/

namespace Blotto.ImplicitLeafCounts.ProposalTree

def constructionDelta (tree : ProposalTree) : ℚ := 1 / (8 * (tree.projected.nodes : ℚ))

theorem constructionDelta_bounds (tree : ProposalTree) : 0 < tree.constructionDelta ∧ tree.constructionDelta ≤ 1 := by
  have hn : (0 : ℚ) < tree.projected.nodes := by exact_mod_cast tree.nodes_positive
  have hOne : (1 : ℚ) ≤ tree.projected.nodes := by exact_mod_cast tree.nodes_positive
  unfold constructionDelta
  constructor
  · positivity
  · apply (div_le_one (by positivity : (0 : ℚ) < 8 * (tree.projected.nodes : ℚ))).mpr
    linarith

theorem constructed_structuralCaps (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (range : ℚ) (hRange : tree.leafRange ≤ (range : ℝ)) :
    tree.constructed.StructuralCaps tree.maximumBlocks tree.maximumWidth (guideCountCap range tree.constructionDelta) :=
  tree.rebuild_structuralCaps hn hz tree.constructionDelta tree.constructionDelta_bounds.1
    tree.constructionDelta_bounds.2 range hRange

theorem constructed_leaf_counts (tree : ProposalTree) : tree.constructed.leaves = tree.leaves ∧ tree.constructed.forks = tree.forks := by
  have hb : ∀ (source : ProposalTree) (gamma : ℚ) (hg : 1 ≤ gamma),
      (source.rebuildGuides gamma hg).leaves = source.leaves ∧ (source.rebuildGuides gamma hg).forks = source.forks := by
    intro source gamma hg
    induction source with
    | leaf data guide g => exact ⟨rfl, rfl⟩
    | fork guide g left right ihL ihR =>
      simp only [rebuildGuides, leaves, forks, ihL.1, ihR.1, ihL.2, ihR.2, and_self]
  exact hb tree tree.constructionGamma tree.constructionGamma_ge_one

theorem constructed_rejectionSeedCap (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (range : ℚ) (hRange : tree.leafRange ≤ (range : ℝ)) (E : ℕ) :
    tree.constructed.rejectionSeedBudget E ≤ tree.constructed.rejectionAttempts E *
      (3 * (tree.leaves * tree.maximumBlocks + tree.forks * guideCountCap range tree.constructionDelta) +
        tree.constructed.rejectionPrecision E * (3 * tree.projected.nodes + tree.leaves * tree.maximumWidth + 3) + 3) := by
  have hb := tree.constructed.rejectionSeedBudget_bound tree.maximumBlocks tree.maximumWidth
    (guideCountCap range tree.constructionDelta) E (tree.constructed_structuralCaps hn hz range hRange)
  rw [tree.constructed_leaf_counts.1, tree.constructed_leaf_counts.2] at hb
  have hNodes : tree.constructed.projected.nodes = tree.projected.nodes := tree.rebuild_nodes _ _
  rw [hNodes] at hb
  exact hb

end Blotto.ImplicitLeafCounts.ProposalTree
