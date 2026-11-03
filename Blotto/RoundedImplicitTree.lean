import Blotto.RoundedProposalLeaf
import Blotto.ConstructedImplicitSeedCap

/-! Nonempty right-comb proposal trees are built from one succinct rounded
leaf per original field. No local code array is enumerated. Balance-dependent
preparation bounds remain separate from this executable source construction. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts

def leafComb : (n : ℕ) → (Fin (n + 1) → ProposalLeaf) → ProposalTree
  | 0, leaves => .leaf (leaves 0) ProductArrayTree.dummyGuide 1
  | n + 1, leaves => .fork ProductArrayTree.dummyGuide 1
      (.leaf (leaves 0) ProductArrayTree.dummyGuide 1) (leafComb n (fun field => leaves field.succ))

theorem leafComb_leaves (n : ℕ) (leaves : Fin (n + 1) → ProposalLeaf) : (leafComb n leaves).leaves = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => change 1 + (leafComb n _).leaves = _; rw [ih]; omega

theorem leafComb_nonnegative (n : ℕ) (leaves : Fin (n + 1) → ProposalLeaf)
    (h : ∀ field (code : Fin ((leaves field).cap + 1)), 0 ≤ (leaves field).decode code.val) :
    (leafComb n leaves).NonnegativeResources := by
  induction n with
  | zero => exact h 0
  | succ n ih => exact ⟨h 0, ih _ (fun field => h field.succ)⟩

theorem leafComb_zero (n : ℕ) (leaves : Fin (n + 1) → ProposalLeaf)
    (h : ∀ field, (leaves field).decode 0 = 0) : (leafComb n leaves).ZeroResources := by
  induction n with
  | zero => exact h 0
  | succ n ih => exact ⟨h 0, ih _ (fun field => h field.succ)⟩

theorem leafComb_fields (n : ℕ) (leaves : Fin (n + 1) → ProposalLeaf)
    (h : ∀ field (code : Fin ((leaves field).cap + 1)), 0 ≤ (leaves field).decode code.val) :
    ((leafComb n leaves).allocationTree (leafComb_nonnegative n leaves h)).fields = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 1 + ((leafComb n (fun field => leaves field.succ)).allocationTree _).fields = _
    rw [ih _ (fun field => h field.succ)]
    omega

theorem leafComb_range (n : ℕ) (leaves : Fin (n + 1) → ProposalLeaf) :
    (leafComb n leaves).leafRange = ∑ field : Fin (n + 1),
      Real.log ((totalMass (leaves field).blocks : ℝ) / (prefixMass (leaves field).blocks 0 : ℝ)) := by
  induction n with
  | zero => simp [leafComb, ProposalTree.leafRange]
  | succ n ih =>
    change Real.log ((totalMass (leaves 0).blocks : ℝ) / (prefixMass (leaves 0).blocks 0 : ℝ)) + (leafComb n _).leafRange = _
    rw [ih]
    exact (Fin.sum_univ_succ (fun field : Fin ((n + 1) + 1) =>
      Real.log ((totalMass (leaves field).blocks : ℝ) / (prefixMass (leaves field).blocks 0 : ℝ)))).symm

theorem leafComb_maximumBlocks (n : ℕ) (leaves : Fin (n + 1) → ProposalLeaf) (B : ℕ)
    (h : ∀ field, (leaves field).blocks.length - 1 ≤ B) : (leafComb n leaves).maximumBlocks ≤ B := by
  induction n with
  | zero => exact h 0
  | succ n ih => exact max_le (h 0) (ih _ (fun field => h field.succ))

theorem leafComb_maximumWidth (n : ℕ) (leaves : Fin (n + 1) → ProposalLeaf) (W : ℕ)
    (h : ∀ field, offsetWidth (leaves field).cap ≤ W) : (leafComb n leaves).maximumWidth ≤ W := by
  induction n with
  | zero => exact h 0
  | succ n ih => exact max_le (h 0) (ih _ (fun field => h field.succ))

def roundedTree {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) : ProposalTree :=
  leafComb n (roundedProposalLeaf caps decode hm selected opponent eta theta heta htheta past)

theorem roundedTree_nonnegative {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code) :
    (roundedTree n caps decode hm selected opponent eta theta heta htheta past).NonnegativeResources :=
  leafComb_nonnegative n _ (fun field code => hn field code.val (by have hc := code.isLt; change code.val < caps field + 1 at hc; omega))

theorem roundedTree_zero {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (hz : ∀ field, decode field 0 = 0) :
    (roundedTree n caps decode hm selected opponent eta theta heta htheta past).ZeroResources := leafComb_zero n _ hz

theorem roundedTree_range_bound {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) :
    (roundedTree n caps decode hm selected opponent eta theta heta htheta past).leafRange ≤
      (∑ field : Fin (n + 1), Real.log ((caps field + 1 : ℕ) : ℝ)) +
        ((eta : ℝ) + 3 * (theta : ℝ)) * past.length := by
  unfold roundedTree
  rw [leafComb_range]
  have hEach : ∀ field : Fin (n + 1), Real.log
      ((totalMass (resourceBlockHistory caps decode selected opponent eta theta past field) : ℝ) /
        (prefixMass (resourceBlockHistory caps decode selected opponent eta theta past field) 0 : ℝ)) ≤
      Real.log ((caps field + 1 : ℕ) : ℝ) + (SparseMW.fieldUpdateCount selected past field : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ)) := by
    intro field
    exact rounded_history_log_range (sizes := fun field => caps field + 1) selected
      (resourceLoss caps decode selected opponent) eta theta heta htheta (resourceLoss_unit caps decode selected opponent)
      past field (caps field) rfl _ (resourceBlockHistory_partition caps decode selected opponent eta theta past field)
      (resourceBlockHistory_positive caps decode selected opponent eta theta heta htheta past field)
      (resourceBlockHistory_refines caps decode hm selected opponent eta theta past field)
  have hSum := Finset.sum_le_sum (fun field (_h : field ∈ (Finset.univ : Finset (Fin (n + 1)))) => hEach field)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hSum
  have hCounts : (∑ field : Fin (n + 1), (SparseMW.fieldUpdateCount selected past field : ℝ)) = past.length := by
    exact_mod_cast SparseMW.fieldUpdateCount_sum selected past
  rw [hCounts] at hSum
  change (∑ field : Fin (n + 1), Real.log
    ((totalMass (resourceBlockHistory caps decode selected opponent eta theta past field) : ℝ) /
      (prefixMass (resourceBlockHistory caps decode selected opponent eta theta past field) 0 : ℝ))) ≤ _
  simpa only [mul_comm] using hSum

theorem roundedTree_maximumBlocks {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (T : ℕ) (hT : past.length ≤ T) :
    (roundedTree n caps decode hm selected opponent eta theta heta htheta past).maximumBlocks ≤ 2 * T := by
  apply leafComb_maximumBlocks
  intro field
  have hb := resourceBlockHistory_length caps decode selected opponent eta theta past field
  have hc := (fieldUpdateCount_le_length selected past field).trans hT
  change (resourceBlockHistory caps decode selected opponent eta theta past field).length - 1 ≤ _
  omega

theorem logNat_le_binaryWordWidth (N : ℕ) (hN : 0 < N) : Real.log (N : ℝ) ≤ (binaryWordWidth N : ℝ) := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have hUpper : (N : ℝ) ≤ (2 : ℝ) ^ binaryWordWidth N := by exact_mod_cast (lt_pow_binaryWordWidth N).le
  have hLog := Real.log_le_log hp hUpper
  rw [Real.log_pow] at hLog
  have hTwo : Real.log (2 : ℝ) ≤ 1 := by
    have he := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at he ⊢
    exact he
  exact hLog.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hTwo (Nat.cast_nonneg (binaryWordWidth N)))

theorem offsetWidth_le_binaryWordWidth (C : ℕ) : offsetWidth C ≤ binaryWordWidth (C + 1) := by
  unfold offsetWidth UniformNatRejection.width
  apply widthRatioPrecision_minimal (C + 1) 1 _ (by omega) (by decide)
  simpa only [one_mul] using (lt_pow_binaryWordWidth (C + 1)).le

theorem roundedTree_maximumWidth {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (A : ℕ) (hA : ∀ field, binaryWordWidth (caps field + 1) ≤ A) :
    (roundedTree n caps decode hm selected opponent eta theta heta htheta past).maximumWidth ≤ A :=
  leafComb_maximumWidth n _ A (fun field => (offsetWidth_le_binaryWordWidth (caps field)).trans (hA field))

def roundedRange (m : ℕ) (caps : Fin m → ℕ) (eta theta : ℚ) (T : ℕ) : ℚ :=
  (∑ field, binaryWordWidth (caps field + 1) : ℕ) + (eta + 3 * theta) * T

def roundedNatRange (m : ℕ) (caps : Fin m → ℕ) (T : ℕ) : ℕ :=
  (∑ field, binaryWordWidth (caps field + 1)) + 2 * T

theorem roundedTree_horizon_range {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (T : ℕ) (hT : past.length ≤ T) :
    (roundedTree n caps decode hm selected opponent eta theta heta htheta past).leafRange ≤
      (roundedRange (n + 1) caps eta theta T : ℝ) := by
  have he := roundedTree_range_bound n caps decode hm selected opponent eta theta heta htheta past
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

theorem roundedTree_horizon_range_nat {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (T : ℕ) (hT : past.length ≤ T) :
    (roundedTree n caps decode hm selected opponent eta theta heta htheta past).leafRange ≤
      (roundedNatRange (n + 1) caps T : ℝ) := by
  have he := roundedTree_horizon_range n caps decode hm selected opponent eta theta heta htheta past T hT
  have hDecay : eta + 3 * theta ≤ 2 := by linarith [heta.2, htheta.2]
  have hNat : roundedRange (n + 1) caps eta theta T ≤ (roundedNatRange (n + 1) caps T : ℚ) := by
    unfold roundedRange roundedNatRange
    push_cast
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hDecay (Nat.cast_nonneg T))
  exact he.trans (by exact_mod_cast hNat)

end ImplicitLeafCounts
end Blotto
