import Blotto.GenericImplicitBlockHistory
import Blotto.RoundedImplicitSeedSchedule

/-! Arbitrary raw observation histories instantiate the succinct implicit draw's
polynomial seed cap. All block, range, and width bounds follow from the native
rounded updates; no finite encoding of observations is used. Complete binary
preparation costs and continuous-game compilation remain separate. -/

namespace Blotto.ImplicitLeafCounts
open scoped BigOperators

def genericTree {α : Type*} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List α) : ProposalTree :=
  leafComb n (genericLeaf caps decode hm selected opponent eta theta heta htheta past)

theorem genericTree_nonnegative {α : Type*} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List α) (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code) :
    (genericTree n caps decode hm selected opponent eta theta heta htheta past).NonnegativeResources :=
  leafComb_nonnegative n _ (fun field code => hn field code.val (by have hc := code.isLt; change code.val < caps field + 1 at hc; omega))

theorem genericTree_zero {α : Type*} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List α) (hz : ∀ field, decode field 0 = 0) :
    (genericTree n caps decode hm selected opponent eta theta heta htheta past).ZeroResources := leafComb_zero n _ hz

theorem genericTree_range_bound {α : Type*} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List α) :
    (genericTree n caps decode hm selected opponent eta theta heta htheta past).leafRange ≤
      (∑ field : Fin (n + 1), Real.log ((caps field + 1 : ℕ) : ℝ)) +
        ((eta : ℝ) + 3 * (theta : ℝ)) * past.length := by
  unfold genericTree
  rw [leafComb_range]
  have hEach : ∀ field : Fin (n + 1), Real.log
      ((totalMass (genericBlocks caps decode selected opponent eta theta past field) : ℝ) /
        (prefixMass (genericBlocks caps decode selected opponent eta theta past field) 0 : ℝ)) ≤
      Real.log ((caps field + 1 : ℕ) : ℝ) + (genericCount selected past field : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ)) := by
    intro field
    exact genericBlocks_log_range caps decode hm selected opponent eta theta heta htheta past field
  have hSum := Finset.sum_le_sum (fun field (_h : field ∈ (Finset.univ : Finset (Fin (n + 1)))) => hEach field)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hSum
  have hCounts : (∑ field : Fin (n + 1), (genericCount selected past field : ℝ)) = past.length := by
    exact_mod_cast genericCount_sum selected past
  rw [hCounts] at hSum
  change (∑ field : Fin (n + 1), Real.log
    ((totalMass (genericBlocks caps decode selected opponent eta theta past field) : ℝ) /
      (prefixMass (genericBlocks caps decode selected opponent eta theta past field) 0 : ℝ))) ≤ _
  simpa only [mul_comm] using hSum

theorem genericTree_maximumBlocks {α : Type*} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List α) (T : ℕ) (hT : past.length ≤ T) :
    (genericTree n caps decode hm selected opponent eta theta heta htheta past).maximumBlocks ≤ 2 * T := by
  apply leafComb_maximumBlocks
  intro field
  have hb := genericBlocks_length caps decode selected opponent eta theta past field
  have hc := (genericCount_le_length selected past field).trans hT
  change (genericBlocks caps decode selected opponent eta theta past field).length - 1 ≤ _
  omega

theorem genericTree_maximumWidth {α : Type*} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List α) (A : ℕ) (hA : ∀ field, binaryWordWidth (caps field + 1) ≤ A) :
    (genericTree n caps decode hm selected opponent eta theta heta htheta past).maximumWidth ≤ A :=
  leafComb_maximumWidth n _ A (fun field => (offsetWidth_le_binaryWordWidth (caps field)).trans (hA field))

theorem genericTree_horizon_range {α : Type*} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List α) (T : ℕ) (hT : past.length ≤ T) :
    (genericTree n caps decode hm selected opponent eta theta heta htheta past).leafRange ≤
      (roundedRange (n + 1) caps eta theta T : ℝ) := by
  have he := genericTree_range_bound n caps decode hm selected opponent eta theta heta htheta past
  have hLog : (∑ field : Fin (n + 1), Real.log ((caps field + 1 : ℕ) : ℝ)) ≤
      ((∑ field : Fin (n + 1), binaryWordWidth (caps field + 1) : ℕ) : ℝ) := by
    push_cast
    exact Finset.sum_le_sum (fun field _ => by
      simpa only [Nat.cast_add, Nat.cast_one] using logNat_le_binaryWordWidth (caps field + 1) (by omega))
  have hEta : (0 : ℝ) ≤ (eta : ℝ) + 3 * (theta : ℝ) := by exact_mod_cast (show (0 : ℚ) ≤ eta + 3 * theta by linarith [heta.1, htheta.1])
  have hTime : (past.length : ℝ) ≤ T := by exact_mod_cast hT
  have hDecay := mul_le_mul_of_nonneg_left hTime hEta
  have hTarget : (roundedRange (n + 1) caps eta theta T : ℝ) =
      ((∑ field : Fin (n + 1), binaryWordWidth (caps field + 1) : ℕ) : ℝ) + ((eta : ℝ) + 3 * (theta : ℝ)) * T := by
    simp [roundedRange]
  rw [hTarget]
  linarith

theorem genericTree_horizon_range_nat {α : Type*} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List α) (T : ℕ) (hT : past.length ≤ T) :
    (genericTree n caps decode hm selected opponent eta theta heta htheta past).leafRange ≤
      (roundedNatRange (n + 1) caps T : ℝ) := by
  have he := genericTree_horizon_range n caps decode hm selected opponent eta theta heta htheta past T hT
  have hDecay : eta + 3 * theta ≤ 2 := by linarith [heta.2, htheta.2]
  have hNat : roundedRange (n + 1) caps eta theta T ≤ (roundedNatRange (n + 1) caps T : ℚ) := by
    unfold roundedRange roundedNatRange
    push_cast
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hDecay (Nat.cast_nonneg T))
  exact he.trans (by exact_mod_cast hNat)
theorem genericTree_polynomial_seed_bound {α : Type*} (n : ℕ) (caps : Fin (n + 1) → ℕ)
    (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code)
    (hz : ∀ field, decode field 0 = 0)
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List α) (T A E : ℕ) (hT : past.length ≤ T)
    (hA : ∀ field, binaryWordWidth (caps field + 1) ≤ A) :
    (genericTree n caps decode hm selected opponent eta theta heta htheta past).constructed.rejectionSeedBudget E ≤
      ProposalTree.polynomialSeedCap (n + 1) (2 * n + 1) T A (roundedNatRange (n + 1) caps T) E := by
  let tree := genericTree n caps decode hm selected opponent eta theta heta htheta past
  have hNonnegative := genericTree_nonnegative n caps decode hm selected opponent eta theta heta htheta past hn
  have hZero := genericTree_zero n caps decode hm selected opponent eta theta heta htheta past hz
  have hBlocks := genericTree_maximumBlocks n caps decode hm selected opponent eta theta heta htheta past T hT
  have hWidth := genericTree_maximumWidth n caps decode hm selected opponent eta theta heta htheta past A hA
  have hRange := genericTree_horizon_range_nat n caps decode hm selected opponent eta theta heta htheta past T hT
  have he := tree.constructed_polynomial_seed_bound hNonnegative hZero T A (roundedNatRange (n + 1) caps T) E hBlocks hWidth hRange
  have hLeaves : tree.leaves = n + 1 := leafComb_leaves n _
  have hNodes : tree.projected.nodes = 2 * n + 1 := leafComb_nodes n _
  rw [hLeaves, hNodes] at he
  exact he

theorem genericTree_uniform_horizon_seed_bound {α : Type*} (n : ℕ) (caps : Fin (n + 1) → ℕ)
    (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code)
    (hz : ∀ field, decode field 0 = 0)
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List α) (T A E : ℕ) (hT : past.length ≤ T)
    (hA : ∀ field, binaryWordWidth (caps field + 1) ≤ A) :
    (genericTree n caps decode hm selected opponent eta theta heta htheta past).constructed.rejectionSeedBudget E ≤
      ProposalTree.polynomialSeedCap (n + 1) (2 * n + 1) T A ((n + 1) * A + 2 * T) E :=
  (genericTree_polynomial_seed_bound n caps decode hm hn hz selected opponent eta theta heta htheta past T A E hT hA).trans
    (polynomialSeedCap_range_mono _ _ _ _ _ _ _ (roundedNatRange_uniform_bound n caps T A hA))

theorem genericTree_epsilon_horizon_seed_bound {α : Type*} (n : ℕ) (caps : Fin (n + 1) → ℕ)
    (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code)
    (hz : ∀ field, decode field 0 = 0)
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List α) (T A : ℕ) (hT : past.length ≤ T)
    (hA : ∀ field, binaryWordWidth (caps field + 1) ≤ A) (epsilon : ℚ) (he : 0 < epsilon) :
    (genericTree n caps decode hm selected opponent eta theta heta htheta past).constructed.epsilonSeedBudget epsilon ≤
      ProposalTree.polynomialSeedCap (n + 1) (2 * n + 1) T A ((n + 1) * A + 2 * T)
        (6 + binaryWordWidth (32 * epsilon).den) := by
  have hBound := genericTree_uniform_horizon_seed_bound n caps decode hm hn hz selected opponent eta theta heta htheta
    past T A (RationalWeightedGuideTree.epsilonPrecision epsilon) hT hA
  have hPrecision : RationalWeightedGuideTree.epsilonPrecision epsilon ≤ 6 + binaryWordWidth (32 * epsilon).den :=
    accuracyPrecision_denominator_width _ (by positivity)
  exact hBound.trans (polynomialSeedCap_precision_mono _ _ _ _ _ _ _ hPrecision)

end Blotto.ImplicitLeafCounts
