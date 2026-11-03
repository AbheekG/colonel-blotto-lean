import Blotto.GroupedGuideCertificate

/-! Actual merge sorting, complete tie grouping and deterministic lower-guide
pruning for arbitrary labelled rational atoms. Sorting permutes occurrences;
only the subsequent full resource groups combine their masses. -/

namespace Blotto
open scoped Classical

namespace CumulativeGuideSorting
open CumulativeGuidePruning CumulativeResourceGrouping

def sort (atoms : List Atom) : List Atom :=
  atoms.mergeSort (fun a b => decide (a.1 ≤ b.1))

theorem sort_perm (atoms : List Atom) : (sort atoms).Perm atoms :=
  List.mergeSort_perm atoms _

theorem sort_nondecreasing (atoms : List Atom) : Nondecreasing (sort atoms) := by
  have he := List.pairwise_mergeSort
    (le := fun a b : Atom => decide (a.1 ≤ b.1))
    (fun a b c hab hbc => by
      have hab' : a.1 ≤ b.1 := of_decide_eq_true hab
      have hbc' : b.1 ≤ c.1 := of_decide_eq_true hbc
      exact decide_eq_true (hab'.trans hbc'))
    (fun a b => by
      rcases le_total a.1 b.1 with hab | hba
      · simp only [decide_eq_true hab, Bool.true_or]
      · simp only [decide_eq_true hba, Bool.or_true]) atoms
  simpa only [sort, Nondecreasing, decide_eq_true_eq] using he

theorem prefixMass_eq_list_sum (atoms : List Atom) (t : ℝ) :
    prefixMass atoms t = (atoms.map (fun a => if (a.1 : ℝ) ≤ t then a.2 else 0)).sum := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    simpa only [prefixMass, List.map_cons, List.sum_cons] using
      congrArg (fun x => (if (atom.1 : ℝ) ≤ t then atom.2 else 0) + x) ih

theorem perm_prefixMass {atoms other : List Atom} (h : atoms.Perm other) (t : ℝ) :
    prefixMass atoms t = prefixMass other t := by
  rw [prefixMass_eq_list_sum, prefixMass_eq_list_sum]
  exact (h.map _).sum_eq

theorem perm_nonnegative {atoms other : List Atom} (h : atoms.Perm other)
    (hn : Nonnegative other) : Nonnegative atoms :=
  fun atom ha => hn atom (h.mem_iff.mp ha)

theorem sort_prefixMass (atoms : List Atom) (t : ℝ) :
    prefixMass (sort atoms) t = prefixMass atoms t := perm_prefixMass (sort_perm atoms) t

theorem sort_nonnegative (atoms : List Atom) (h : Nonnegative atoms) :
    Nonnegative (sort atoms) := perm_nonnegative (sort_perm atoms) h

theorem sort_length (atoms : List Atom) : (sort atoms).length = atoms.length :=
  (sort_perm atoms).length_eq

def guideAtoms (atoms : List Atom) (gamma : ℚ) : List Atom :=
  prune gamma (group (sort atoms))

theorem guideAtoms_nonnegative (atoms : List Atom) (gamma : ℚ) (h : Nonnegative atoms) :
    Nonnegative (guideAtoms atoms gamma) :=
  prune_nonnegative _ gamma (group_nonnegative _ (sort_nonnegative atoms h))

theorem guideAtoms_strictly_grouped (atoms : List Atom) (gamma : ℚ) :
    StrictlyGrouped (guideAtoms atoms gamma) :=
  prune_strictly_grouped _ gamma (group_strictly_grouped _ (sort_nondecreasing atoms))

theorem guideAtoms_length_le (atoms : List Atom) (gamma : ℚ) :
    (guideAtoms atoms gamma).length ≤ atoms.length := by
  exact (prune_length_le _ gamma).trans
    ((group_length_le _).trans (le_of_eq (sort_length atoms)))

theorem guideAtoms_envelope (atoms : List Atom) (gamma : ℚ) (hg : 1 ≤ gamma)
    (h : Nonnegative atoms) (t : ℝ) :
    prefixMass (guideAtoms atoms gamma) t ≤ prefixMass atoms t ∧
      prefixMass atoms t ≤ gamma * prefixMass (guideAtoms atoms gamma) t := by
  have he := grouped_prune_envelope (sort atoms) gamma hg (sort_nonnegative atoms h)
    (sort_nondecreasing atoms) t
  rw [sort_prefixMass] at he
  exact he

theorem guideAtoms_zero_iff (atoms : List Atom) (gamma : ℚ) (hg : 1 ≤ gamma)
    (h : Nonnegative atoms) (t : ℝ) :
    prefixMass (guideAtoms atoms gamma) t = 0 ↔ prefixMass atoms t = 0 := by
  have he := grouped_prune_zero_iff (sort atoms) gamma hg (sort_nonnegative atoms h)
    (sort_nondecreasing atoms) t
  rw [sort_prefixMass] at he
  exact he

def guideFamily (atoms : List Atom) (gamma : ℚ) (h : Nonnegative atoms) :
    RationalWeightedFamily (guideAtoms atoms gamma).length :=
  rationalFamily _ (guideAtoms_nonnegative atoms gamma h)

noncomputable def guideLeaf (atoms : List Atom) (gamma : ℚ) (h : Nonnegative atoms) : WeightedGuideTree :=
  .leaf (rationalFamily atoms h).real (guideFamily atoms gamma h).real gamma

theorem guideLeaf_certified (atoms : List Atom) (gamma : ℚ) (hg : 1 ≤ gamma)
    (h : Nonnegative atoms) : (guideLeaf atoms gamma h).LowerCertified := by
  refine WeightedGuideTree.leaf_lower_certified _ _ _ (by exact_mod_cast hg) ?_ ?_
  · intro t
    unfold guideFamily
    rw [rationalFamily_prefix_real, rationalFamily_prefix_real]
    exact_mod_cast (guideAtoms_envelope atoms gamma hg h t).1
  · intro t
    unfold guideFamily
    rw [rationalFamily_prefix_real, rationalFamily_prefix_real]
    exact_mod_cast (guideAtoms_envelope atoms gamma hg h t).2

end CumulativeGuideSorting
end Blotto
