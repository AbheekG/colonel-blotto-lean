import Blotto.CumulativeResourceGrouping
import Blotto.CumulativeGuideFamily

/-! Sorting remains a caller operation. Once atoms are nondecreasing, exact
adjacent tie grouping and rational pruning construct a certified lower guide
for the original labelled family, without losing zero resource ties. -/

namespace Blotto
open scoped BigOperators
namespace CumulativeResourceGrouping
open CumulativeGuidePruning

def lowerGuide (atoms : List Atom) (gamma : ℚ) (h : Nonnegative atoms) :
    RationalWeightedFamily (prune gamma (group atoms)).length :=
  prunedFamily (group atoms) gamma (group_nonnegative atoms h)

noncomputable def lowerGuideLeaf (atoms : List Atom) (gamma : ℚ) (h : Nonnegative atoms) : WeightedGuideTree :=
  .leaf (rationalFamily atoms h).real (lowerGuide atoms gamma h).real gamma

theorem lowerGuideLeaf_certified (atoms : List Atom) (gamma : ℚ) (hg : 1 ≤ gamma)
    (h : Nonnegative atoms) (hs : Nondecreasing atoms) :
    (lowerGuideLeaf atoms gamma h).LowerCertified := by
  refine WeightedGuideTree.leaf_lower_certified _ _ _ (by exact_mod_cast hg) ?_ ?_
  · intro t
    unfold lowerGuide prunedFamily
    rw [rationalFamily_prefix_real, rationalFamily_prefix_real]
    exact_mod_cast (grouped_prune_envelope atoms gamma hg h hs t).1
  · intro t
    unfold lowerGuide prunedFamily
    rw [rationalFamily_prefix_real, rationalFamily_prefix_real]
    exact_mod_cast (grouped_prune_envelope atoms gamma hg h hs t).2

theorem lowerGuide_size (atoms : List Atom) (gamma : ℚ) :
    (prune gamma (group atoms)).length ≤ atoms.length :=
  (prune_length_le (group atoms) gamma).trans (group_length_le atoms)

end CumulativeResourceGrouping
end Blotto
