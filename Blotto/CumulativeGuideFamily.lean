import Blotto.CumulativeGuidePruning
import Blotto.RationalWeightedGuideTree

/-! Actual grouped-list pruning supplies the lower-guide leaf certificate.
The finite-family view preserves every atom label and exact weak threshold. -/

namespace Blotto
open scoped BigOperators
namespace CumulativeGuidePruning

def rationalFamily (groups : List Atom) (h : Nonnegative groups) : RationalWeightedFamily groups.length where
  resource := fun i => (groups[i]).1
  mass := fun i => (groups[i]).2
  mass_nonnegative := fun i => h _ (List.getElem_mem i.isLt)

theorem prefixMass_eq_sum (groups : List Atom) (t : ℝ) :
    prefixMass groups t = ∑ i : Fin groups.length, if (groups[i].1 : ℝ) ≤ t then groups[i].2 else 0 := by
  induction groups with
  | nil => simp [prefixMass]
  | cons atom rest ih =>
    change prefixMass (atom :: rest) t =
      ∑ i : Fin (rest.length + 1), if ((atom :: rest)[i].1 : ℝ) ≤ t then (atom :: rest)[i].2 else 0
    rw [Fin.sum_univ_succ]
    simp only [prefixMass]
    rw [ih]
    rfl

theorem rationalFamily_prefix_real (groups : List Atom) (h : Nonnegative groups) (t : ℝ) :
    (rationalFamily groups h).real.prefixMass t = (prefixMass groups t : ℝ) := by
  rw [prefixMass_eq_sum]
  unfold rationalFamily RationalWeightedFamily.real WeightedResourceFamily.prefixMass
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

def prunedFamily (groups : List Atom) (gamma : ℚ) (h : Nonnegative groups) :
    RationalWeightedFamily (prune gamma groups).length :=
  rationalFamily _ (prune_nonnegative groups gamma h)

noncomputable def prunedLeaf (groups : List Atom) (gamma : ℚ) (h : Nonnegative groups) : WeightedGuideTree :=
  .leaf (rationalFamily groups h).real (prunedFamily groups gamma h).real gamma

theorem prunedLeaf_certified (groups : List Atom) (gamma : ℚ) (hg : 1 ≤ gamma)
    (h : Nonnegative groups) (hs : StrictlyGrouped groups) :
    (prunedLeaf groups gamma h).LowerCertified := by
  refine WeightedGuideTree.leaf_lower_certified _ _ _ (by exact_mod_cast hg) ?_ ?_
  · intro t
    rw [rationalFamily_prefix_real]
    unfold prunedFamily
    rw [rationalFamily_prefix_real]
    exact (prune_real_envelope groups gamma hg h hs t).1
  · intro t
    rw [rationalFamily_prefix_real]
    unfold prunedFamily
    rw [rationalFamily_prefix_real]
    exact (prune_real_envelope groups gamma hg h hs t).2

end CumulativeGuidePruning
end Blotto
