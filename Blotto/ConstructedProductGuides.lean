import Blotto.ProductAllocationDecoder
import Blotto.CumulativeInternalGuide
import Blotto.GuideAccuracyBudget

/-! Every local guide is actually constructed by exact sorting/grouping/pruning
at one rational gamma. Rebuilding preserves the complete labelled bid universe;
certification is derived recursively, not supplied as an input assumption. Pair
enumeration remains the charged conservative construction, not fast R161. -/

namespace Blotto
open scoped BigOperators
namespace ProductBidTree

def bidAtoms {n : ℕ} (family : RationalWeightedFamily n) : List CumulativeGuidePruning.Atom :=
  List.ofFn (fun i => (family.resource i, family.mass i))

theorem bidAtoms_nonnegative {n : ℕ} (family : RationalWeightedFamily n) :
    CumulativeGuidePruning.Nonnegative (bidAtoms family) := by
  intro atom ha
  rcases List.mem_ofFn.mp ha with ⟨i, rfl⟩
  exact family.mass_nonnegative i

def rebuildGuides (gamma : ℚ) : ProductBidTree → ProductBidTree
  | .leaf family hn _ _ => .leaf family hn
      (CumulativeGuideSorting.guideFamily (bidAtoms family) gamma (bidAtoms_nonnegative family)) gamma
  | .fork _ _ left right =>
      let l := left.rebuildGuides gamma
      let r := right.rebuildGuides gamma
      .fork (CumulativeInternalGuide.internalGuide l.guideTree.guide r.guideTree.guide gamma) gamma l r

theorem rebuild_fields (tree : ProductBidTree) (gamma : ℚ) : (tree.rebuildGuides gamma).fields = tree.fields := by
  induction tree with
  | leaf family hn guide g => rfl
  | fork guide g left right ihL ihR => simp only [rebuildGuides, fields, ihL, ihR]

theorem rebuild_labels (tree : ProductBidTree) (gamma : ℚ) : (tree.rebuildGuides gamma).labels = tree.labels := by
  induction tree with
  | leaf family hn guide g => rfl
  | fork guide g left right ihL ihR => simp only [rebuildGuides, labels, ihL, ihR]

theorem bidAtoms_prefix {n : ℕ} (family : RationalWeightedFamily n) (t : ℝ) :
    (CumulativeGuidePruning.prefixMass (bidAtoms family) t : ℝ) = family.real.prefixMass t := by
  rw [CumulativeGuideSorting.prefixMass_eq_list_sum]
  unfold bidAtoms
  rw [List.map_ofFn, List.sum_ofFn]
  push_cast
  unfold WeightedResourceFamily.prefixMass RationalWeightedFamily.real
  dsimp only
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (family.resource i : ℝ) ≤ t <;> simp [h]

theorem guide_real_prefix (tree : RationalWeightedGuideTree) (t : ℝ) :
    tree.guide.real.prefixMass t = tree.real.guide.prefixMass t := by
  cases tree <;> rfl

theorem guide_real_convolution (left right : RationalWeightedGuideTree) (t : ℝ) :
    left.guide.real.convolution right.guide.real t = left.real.guide.convolution right.real.guide t := by
  cases left <;> cases right <;> rfl

theorem rebuild_certified (tree : ProductBidTree) (gamma : ℚ) (hg : 1 ≤ gamma) :
    (tree.rebuildGuides gamma).guideTree.real.LowerCertified := by
  induction tree with
  | leaf family hn guide g =>
    refine WeightedGuideTree.leaf_lower_certified _ _ _ (by exact_mod_cast hg) ?_ ?_
    · intro t
      have he := CumulativeGuideSorting.guideAtoms_envelope (bidAtoms family) gamma hg (bidAtoms_nonnegative family) t
      change (CumulativeGuideSorting.guideFamily _ _ _).real.prefixMass t ≤ family.real.prefixMass t
      unfold CumulativeGuideSorting.guideFamily
      rw [CumulativeGuidePruning.rationalFamily_prefix_real, ← bidAtoms_prefix family t]
      exact_mod_cast he.1
    · intro t
      have he := CumulativeGuideSorting.guideAtoms_envelope (bidAtoms family) gamma hg (bidAtoms_nonnegative family) t
      change family.real.prefixMass t ≤ (gamma : ℝ) * (CumulativeGuideSorting.guideFamily _ _ _).real.prefixMass t
      unfold CumulativeGuideSorting.guideFamily
      rw [CumulativeGuidePruning.rationalFamily_prefix_real, ← bidAtoms_prefix family t]
      exact_mod_cast he.2
  | fork guide g left right ihL ihR =>
    refine WeightedGuideTree.fork_lower_certified _ _ _ _ (by exact_mod_cast hg) ihL ihR ?_ ?_
    · intro t
      have he := (CumulativeInternalGuide.internalGuide_local_certificate
        (left.rebuildGuides gamma).guideTree.guide (right.rebuildGuides gamma).guideTree.guide gamma hg t).1
      rw [guide_real_convolution] at he
      exact he
    · intro t
      have he := (CumulativeInternalGuide.internalGuide_local_certificate
        (left.rebuildGuides gamma).guideTree.guide (right.rebuildGuides gamma).guideTree.guide gamma hg t).2
      rw [guide_real_convolution] at he
      exact he

end ProductBidTree
end Blotto
