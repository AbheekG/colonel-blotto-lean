import Blotto.CumulativeGuideSorting

/-! Deterministic internal guides enumerate every child-guide Cartesian pair,
then merge-sort, group all exact ties, and prune cumulative heights. Pair
enumeration is explicit; this is not the fast R161 convolution construction. -/

namespace Blotto
open scoped BigOperators Classical

namespace CumulativeInternalGuide
open CumulativeGuidePruning CumulativeGuideSorting

def pairAtoms {n m : ℕ} (left : RationalWeightedFamily n)
    (right : RationalWeightedFamily m) : List Atom :=
  List.ofFn (fun k : Fin (n * m) =>
    let pair := finProdFinEquiv.symm k
    (left.resource pair.1 + right.resource pair.2, left.mass pair.1 * right.mass pair.2))

theorem pairAtoms_length {n m : ℕ} (left : RationalWeightedFamily n)
    (right : RationalWeightedFamily m) : (pairAtoms left right).length = n * m := by
  simp [pairAtoms]

theorem pairAtoms_nonnegative {n m : ℕ} (left : RationalWeightedFamily n)
    (right : RationalWeightedFamily m) : Nonnegative (pairAtoms left right) := by
  intro atom ha
  rcases List.mem_ofFn.mp ha with ⟨k, rfl⟩
  exact mul_nonneg (left.mass_nonnegative _) (right.mass_nonnegative _)

theorem pairAtoms_prefix_real {n m : ℕ} (left : RationalWeightedFamily n)
    (right : RationalWeightedFamily m) (t : ℝ) :
    (prefixMass (pairAtoms left right) t : ℝ) = left.real.convolution right.real t := by
  rw [prefixMass_eq_list_sum]
  unfold pairAtoms
  rw [List.map_ofFn, List.sum_ofFn]
  push_cast
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]
  unfold RationalWeightedFamily.real WeightedResourceFamily.convolution
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change ((if ((left.resource (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1 +
      right.resource (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 : ℚ) : ℝ) ≤ t then
      left.mass (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1 *
        right.mass (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 else 0 : ℚ) : ℝ) =
    if (left.resource i : ℝ) + (right.resource j : ℝ) ≤ t then
      (left.mass i : ℝ) * (right.mass j : ℝ) else 0
  rw [Equiv.symm_apply_apply]
  push_cast
  split_ifs <;> simp

def internalGuide {n m : ℕ} (left : RationalWeightedFamily n)
    (right : RationalWeightedFamily m) (gamma : ℚ) :
    RationalWeightedFamily (guideAtoms (pairAtoms left right) gamma).length :=
  guideFamily (pairAtoms left right) gamma (pairAtoms_nonnegative left right)

theorem internalGuide_size {n m : ℕ} (left : RationalWeightedFamily n)
    (right : RationalWeightedFamily m) (gamma : ℚ) :
    (guideAtoms (pairAtoms left right) gamma).length ≤ n * m := by
  exact (guideAtoms_length_le _ gamma).trans (le_of_eq (pairAtoms_length left right))

theorem internalGuide_local_certificate {n m : ℕ} (left : RationalWeightedFamily n)
    (right : RationalWeightedFamily m) (gamma : ℚ) (hg : 1 ≤ gamma) (t : ℝ) :
    (internalGuide left right gamma).real.prefixMass t ≤ left.real.convolution right.real t ∧
      left.real.convolution right.real t ≤
        (gamma : ℝ) * (internalGuide left right gamma).real.prefixMass t := by
  have he := guideAtoms_envelope (pairAtoms left right) gamma hg
    (pairAtoms_nonnegative left right) t
  unfold internalGuide guideFamily
  rw [rationalFamily_prefix_real]
  constructor
  · rw [← pairAtoms_prefix_real]
    exact_mod_cast he.1
  · rw [← pairAtoms_prefix_real]
    exact_mod_cast he.2

end CumulativeInternalGuide
end Blotto
