import Blotto.ConstructedImplicitSeedCap

/-! Natural source range/width/update caps give an explicit polynomial seed
majorant for the actual constructed rejection sampler. Accuracy contributes
through its precision E, not a numerical code-universe loop. Instantiating these
source caps with the rounded learner is proved separately. -/

namespace Blotto.ImplicitLeafCounts.ProposalTree

theorem guideCountCap_construction (tree : ProposalTree) (R : ℕ) :
    guideCountCap (R : ℚ) tree.constructionDelta ≤ 1 + 16 * tree.projected.nodes * R := by
  have hn : (0 : ℚ) < tree.projected.nodes := by exact_mod_cast tree.nodes_positive
  have he : 1 + 2 * (R : ℚ) / tree.constructionDelta = ((1 + 16 * tree.projected.nodes * R : ℕ) : ℚ) := by
    unfold constructionDelta
    push_cast
    field_simp
    ring
  have hEq : rationalFactorCeiling (((1 + 16 * tree.projected.nodes * R : ℕ) : ℚ)) =
      1 + 16 * tree.projected.nodes * R := by
    simp only [rationalFactorCeiling, Rat.num_natCast, Rat.den_natCast, Int.toNat_natCast, Nat.add_sub_cancel, Nat.div_one]
  unfold guideCountCap
  rw [he, hEq]

def precisionCap (nodes E : ℕ) : ℕ :=
  E + 1 + binaryWordWidth (2 * (E + 1)) + binaryWordWidth (2 * nodes + 1)

theorem constructed_precision_bound (tree : ProposalTree) (E : ℕ) :
    tree.constructed.rejectionPrecision E ≤ precisionCap tree.projected.nodes E := by
  have he := tree.constructed.rejectionPrecision_word_bound E
  have ha := tree.constructed_trials E
  have hn : tree.constructed.projected.nodes = tree.projected.nodes := tree.rebuild_nodes _ _
  rw [hn] at he
  have hw := binaryWordWidth_mono ha
  unfold precisionCap
  omega

def polynomialSeedCap (fields nodes updates codeWidth range E : ℕ) : ℕ :=
  2 * (E + 1) *
    (3 * (fields * (2 * updates) + fields * (1 + 16 * nodes * range)) +
      precisionCap nodes E * (3 * nodes + fields * codeWidth + 3) + 3)

theorem constructed_polynomial_seed_bound (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (T A R E : ℕ) (hBlocks : tree.maximumBlocks ≤ 2 * T) (hWidth : tree.maximumWidth ≤ A)
    (hRange : tree.leafRange ≤ (R : ℝ)) :
    tree.constructed.rejectionSeedBudget E ≤ polynomialSeedCap tree.leaves tree.projected.nodes T A R E := by
  have hb := tree.constructed_rejectionSeedCap hn hz (R : ℚ) (by exact_mod_cast hRange) E
  have hGuide := tree.guideCountCap_construction R
  have hPrecision := tree.constructed_precision_bound E
  have hAttempts := tree.constructed_trials E
  have hForks : tree.forks ≤ tree.leaves := by have he := tree.forks_add_one; omega
  have hFirst : tree.leaves * tree.maximumBlocks + tree.forks * guideCountCap (R : ℚ) tree.constructionDelta ≤
      tree.leaves * (2 * T) + tree.leaves * (1 + 16 * tree.projected.nodes * R) :=
    Nat.add_le_add (Nat.mul_le_mul_left _ hBlocks) (Nat.mul_le_mul hForks hGuide)
  have hInner : 3 * tree.projected.nodes + tree.leaves * tree.maximumWidth + 3 ≤
      3 * tree.projected.nodes + tree.leaves * A + 3 := by
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hWidth) _) _
  have hSecond := Nat.mul_le_mul hPrecision hInner
  have hBody := Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 3 hFirst) hSecond) 3
  exact hb.trans (Nat.mul_le_mul hAttempts hBody)

end Blotto.ImplicitLeafCounts.ProposalTree
