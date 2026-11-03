import Blotto.ConstructedProductGuides

/-! The actual rebuilt guide tree uses a uniform rational tolerance based on
its unchanged number of nodes. Certification and the global factor budget are
derived together; no supplied sketch-validity promise remains. -/

namespace Blotto
open scoped BigOperators
namespace ProductBidTree

def constructionNodes : ProductBidTree → ℕ
  | .leaf _ _ _ _ => 1
  | .fork _ _ left right => 1 + left.constructionNodes + right.constructionNodes

theorem constructionNodes_positive (tree : ProductBidTree) : 0 < tree.constructionNodes := by
  induction tree with
  | leaf family hn guide gamma => exact Nat.zero_lt_one
  | fork guide gamma left right ihL ihR => change 0 < 1 + _ + _; omega

def constructionGamma (tree : ProductBidTree) : ℚ := 1 + 1 / (8 * (tree.constructionNodes : ℚ))

theorem constructionGamma_ge_one (tree : ProductBidTree) : 1 ≤ tree.constructionGamma := by
  unfold constructionGamma
  have hCount : (0 : ℚ) < tree.constructionNodes := by exact_mod_cast tree.constructionNodes_positive
  have he : (0 : ℚ) ≤ 1 / (8 * (tree.constructionNodes : ℚ)) := by positivity
  linarith

theorem rebuild_factor_count (tree : ProductBidTree) (gamma : ℚ) :
    (tree.rebuildGuides gamma).guideTree.real.nodeCount = tree.constructionNodes := by
  induction tree with
  | leaf family hn guide g => rfl
  | fork guide g left right ihL ihR =>
    change ((left.rebuildGuides gamma).guideTree.real.factors ++
      (right.rebuildGuides gamma).guideTree.real.factors ++ [(gamma : ℝ)]).length = 1 + _ + _
    simp only [List.length_append, List.length_singleton]
    change (left.rebuildGuides gamma).guideTree.real.nodeCount +
      (right.rebuildGuides gamma).guideTree.real.nodeCount + 1 = 1 + _ + _
    rw [ihL, ihR]
    omega

theorem rebuild_factors_same (tree : ProductBidTree) (gamma : ℚ) :
    ∀ g ∈ (tree.rebuildGuides gamma).guideTree.real.factors, g = (gamma : ℝ) := by
  induction tree with
  | leaf family hn guide g => intro x hx; simpa only [rebuildGuides, guideTree, RationalWeightedGuideTree.real, WeightedGuideTree.factors, List.mem_singleton] using hx
  | fork guide g left right ihL ihR =>
    intro x hx
    change x ∈ (left.rebuildGuides gamma).guideTree.real.factors ++
      (right.rebuildGuides gamma).guideTree.real.factors ++ [(gamma : ℝ)] at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with (hl | hr) | he
    · exact ihL x hl
    · exact ihR x hr
    · exact he

def constructGuides (tree : ProductBidTree) : ProductBidTree := tree.rebuildGuides tree.constructionGamma

theorem constructGuides_certified (tree : ProductBidTree) : tree.constructGuides.guideTree.real.LowerCertified :=
  tree.rebuild_certified tree.constructionGamma tree.constructionGamma_ge_one

theorem constructGuides_factor (tree : ProductBidTree) : tree.constructGuides.guideTree.real.factor ≤ 8 / 7 := by
  apply WeightedGuideTree.uniform_factor_bound _ tree.constructGuides_certified
  intro gamma hg
  have he := tree.rebuild_factors_same tree.constructionGamma gamma hg
  rw [he]
  change (tree.constructionGamma : ℝ) ≤ 1 + 1 / (8 * (tree.constructGuides.guideTree.real.nodeCount : ℝ))
  unfold constructGuides
  rw [rebuild_factor_count]
  unfold constructionGamma
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]
  exact le_rfl

end ProductBidTree
end Blotto
