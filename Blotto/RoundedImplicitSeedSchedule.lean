import Blotto.RoundedImplicitTree
import Blotto.PolynomialImplicitSeedCap

/-! The actual sparse rounded learner history instantiates every range/block/
width premise of the implicit draw's polynomial seed cap. Monotone nonnegative
zero-preserving decoding is explicit until the Farey implementation is proved.
This is seed storage, not complete binary preparation or FPTAS runtime. -/

namespace Blotto.ImplicitLeafCounts
open scoped BigOperators

theorem leafComb_nodes (n : ℕ) (data : Fin (n + 1) → ProposalLeaf) :
    (leafComb n data).projected.nodes = 2 * n + 1 := by
  have hLeaves := leafComb_leaves n data
  have hForks := (leafComb n data).forks_add_one
  have hNodes := (leafComb n data).nodes_eq
  omega

theorem roundedTree_polynomial_seed_bound {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ)
    (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code)
    (hz : ∀ field, decode field 0 = 0)
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (T A E : ℕ) (hT : past.length ≤ T)
    (hA : ∀ field, binaryWordWidth (caps field + 1) ≤ A) :
    (roundedTree n caps decode hm selected opponent eta theta heta htheta past).constructed.rejectionSeedBudget E ≤
      ProposalTree.polynomialSeedCap (n + 1) (2 * n + 1) T A (roundedNatRange (n + 1) caps T) E := by
  let tree := roundedTree n caps decode hm selected opponent eta theta heta htheta past
  have hNonnegative := roundedTree_nonnegative n caps decode hm selected opponent eta theta heta htheta past hn
  have hZero := roundedTree_zero n caps decode hm selected opponent eta theta heta htheta past hz
  have hBlocks := roundedTree_maximumBlocks n caps decode hm selected opponent eta theta heta htheta past T hT
  have hWidth := roundedTree_maximumWidth n caps decode hm selected opponent eta theta heta htheta past A hA
  have hRange := roundedTree_horizon_range_nat n caps decode hm selected opponent eta theta heta htheta past T hT
  have he := tree.constructed_polynomial_seed_bound hNonnegative hZero T A (roundedNatRange (n + 1) caps T) E hBlocks hWidth hRange
  have hLeaves : tree.leaves = n + 1 := leafComb_leaves n _
  have hNodes : tree.projected.nodes = 2 * n + 1 := leafComb_nodes n _
  rw [hLeaves, hNodes] at he
  exact he

theorem roundedNatRange_uniform_bound (n : ℕ) (caps : Fin (n + 1) → ℕ) (T A : ℕ)
    (hA : ∀ field, binaryWordWidth (caps field + 1) ≤ A) :
    roundedNatRange (n + 1) caps T ≤ (n + 1) * A + 2 * T := by
  have hSum : (∑ field : Fin (n + 1), binaryWordWidth (caps field + 1)) ≤ (n + 1) * A := by
    calc
      _ ≤ ∑ _field : Fin (n + 1), A := Finset.sum_le_sum (fun field _ => hA field)
      _ = _ := by simp
  exact Nat.add_le_add_right hSum _

theorem polynomialSeedCap_range_mono (fields nodes T A first last E : ℕ) (h : first ≤ last) :
    ProposalTree.polynomialSeedCap fields nodes T A first E ≤ ProposalTree.polynomialSeedCap fields nodes T A last E := by
  unfold ProposalTree.polynomialSeedCap
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _)

theorem roundedTree_uniform_horizon_seed_bound {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ)
    (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code)
    (hz : ∀ field, decode field 0 = 0)
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (T A E : ℕ) (hT : past.length ≤ T)
    (hA : ∀ field, binaryWordWidth (caps field + 1) ≤ A) :
    (roundedTree n caps decode hm selected opponent eta theta heta htheta past).constructed.rejectionSeedBudget E ≤
      ProposalTree.polynomialSeedCap (n + 1) (2 * n + 1) T A ((n + 1) * A + 2 * T) E :=
  (roundedTree_polynomial_seed_bound n caps decode hm hn hz selected opponent eta theta heta htheta past T A E hT hA).trans
    (polynomialSeedCap_range_mono _ _ _ _ _ _ _ (roundedNatRange_uniform_bound n caps T A hA))

theorem polynomialSeedCap_precision_mono (fields nodes T A R first last : ℕ) (h : first ≤ last) :
    ProposalTree.polynomialSeedCap fields nodes T A R first ≤ ProposalTree.polynomialSeedCap fields nodes T A R last := by
  have hTwice : 2 * (first + 1) ≤ 2 * (last + 1) := by omega
  have hWord := binaryWordWidth_mono hTwice
  have hPrecision : ProposalTree.precisionCap nodes first ≤ ProposalTree.precisionCap nodes last := by
    unfold ProposalTree.precisionCap
    omega
  unfold ProposalTree.polynomialSeedCap
  apply Nat.mul_le_mul hTwice
  apply Nat.add_le_add_right
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hPrecision) _

theorem roundedTree_epsilon_horizon_seed_bound {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ)
    (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code)
    (hz : ∀ field, decode field 0 = 0)
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (T A : ℕ) (hT : past.length ≤ T)
    (hA : ∀ field, binaryWordWidth (caps field + 1) ≤ A) (epsilon : ℚ) (he : 0 < epsilon) :
    (roundedTree n caps decode hm selected opponent eta theta heta htheta past).constructed.epsilonSeedBudget epsilon ≤
      ProposalTree.polynomialSeedCap (n + 1) (2 * n + 1) T A ((n + 1) * A + 2 * T)
        (6 + binaryWordWidth (32 * epsilon).den) := by
  have hBound := roundedTree_uniform_horizon_seed_bound n caps decode hm hn hz selected opponent eta theta heta htheta
    past T A (RationalWeightedGuideTree.epsilonPrecision epsilon) hT hA
  have hPrecision : RationalWeightedGuideTree.epsilonPrecision epsilon ≤ 6 + binaryWordWidth (32 * epsilon).den :=
    accuracyPrecision_denominator_width _ (by positivity)
  exact hBound.trans (polynomialSeedCap_precision_mono _ _ _ _ _ _ _ hPrecision)

end Blotto.ImplicitLeafCounts
