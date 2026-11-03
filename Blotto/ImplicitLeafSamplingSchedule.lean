import Blotto.ImplicitResourceSampler
import Blotto.ResourceBlockHistory
import Blotto.RationalEpsilonRejection

/-! A native rational tolerance selects both independent prefix-draw error
budgets. Generated rounded histories derive the finite seed cap from sparse
block growth, rather than requiring a caller's numerical-label bit cap. Whole
tree/internal guide budgets and finite-binary arithmetic costs remain separate. -/

namespace Blotto.ImplicitLeafCounts

def leafPrecision (epsilon : ℚ) : ℕ := RationalWeightedGuideTree.epsilonPrecision (epsilon / 2)

theorem leafPrecision_error (epsilon : ℚ) (he : 0 < epsilon) :
    1 / (2 : ℝ) ^ leafPrecision epsilon + 1 / (2 : ℝ) ^ leafPrecision epsilon ≤ (epsilon : ℝ) := by
  have hg := RationalWeightedGuideTree.epsilonPrecision_guard (epsilon / 2) (by positivity)
  have heq : ((epsilon / 2 : ℚ) : ℝ) = (epsilon : ℝ) / 2 := by norm_cast
  rw [heq] at hg
  change 1 / (2 : ℝ) ^ leafPrecision epsilon ≤ (epsilon : ℝ) / 2 at hg
  linarith

theorem accuracyPrecision_denominator_width (accuracy : ℚ) (ha : 0 < accuracy) :
    rationalAccuracyPrecision accuracy ≤ 6 + binaryWordWidth accuracy.den := by
  have hn : 0 < accuracy.num.toNat := Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr ha)
  have hLarge : 32 * accuracy.den < 2 ^ binaryWordWidth (32 * accuracy.den) := lt_pow_binaryWordWidth _
  have hScale : 32 * accuracy.den ≤ accuracy.num.toNat * 2 ^ binaryWordWidth (32 * accuracy.den) := by
    have hp := Nat.mul_le_mul_right (2 ^ binaryWordWidth (32 * accuracy.den)) hn
    omega
  have he := binaryRatioPrecision_minimal (32 * accuracy.den) accuracy.num.toNat hn _ hScale
  have hWidth := binaryWordWidth_mul 32 accuracy.den
  have h32 : binaryWordWidth 32 = 6 := by decide
  rw [h32] at hWidth
  exact he.trans hWidth

theorem leafPrecision_denominator_width (epsilon : ℚ) (he : 0 < epsilon) :
    leafPrecision epsilon ≤ 6 + binaryWordWidth (16 * epsilon).den := by
  have hEq : (32 : ℚ) * (epsilon / 2) = 16 * epsilon := by ring
  unfold leafPrecision RationalWeightedGuideTree.epsilonPrecision
  rw [hEq]
  exact accuracyPrecision_denominator_width _ (by positivity)

def scheduledPrefixBitBudget (C B : ℕ) (epsilon : ℚ) : ℕ :=
  prefixSampleBitBudget C B (leafPrecision epsilon) (leafPrecision epsilon)

theorem scheduledPrefixBitBudget_bound (C B updates : ℕ) (epsilon : ℚ) (hB : B ≤ 1 + 2 * updates) :
    scheduledPrefixBitBudget C B epsilon ≤
      6 * updates + leafPrecision epsilon * (3 + offsetWidth C) := by
  unfold scheduledPrefixBitBudget prefixSampleBitBudget
  simp only [Nat.mul_add]
  have hComm : leafPrecision epsilon * 3 = 3 * leafPrecision epsilon := Nat.mul_comm _ _
  rw [hComm]
  omega

theorem scheduled_resource_mean_error (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (budget : ℚ) (hFirst : decode 0 ≤ budget) (epsilon : ℚ) (he : 0 < epsilon)
    (test : Fin (C + 1) → ℝ) (hTest : ∀ code, 0 ≤ test code ∧ test code ≤ 1) :
    |(fairBitKernel (scheduledPrefixBitBudget C blocks.length epsilon)).mean
      (fun bits => test (resourceSample C blocks hp hw decode hm budget hFirst
        (leafPrecision epsilon) (leafPrecision epsilon) bits)) -
      (∑ code : Fin (C + 1), if decode code.val ≤ budget then (labelMass blocks code.val : ℝ) * test code else 0) /
        ((decodedFamily C blocks (fun b hb => (hw b hb).le) decode).prefixMass budget : ℝ)| ≤ (epsilon : ℝ) :=
  (resourceSample_mean_error C blocks hp hw decode hm budget hFirst _ _ test hTest).trans
    (leafPrecision_error epsilon he)

theorem resourceBlockHistory_leafBitBudget {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta epsilon : ℚ) (past : List (Fin a)) (field : Fin m) :
    scheduledPrefixBitBudget (caps field)
      (resourceBlockHistory caps decode selected opponent eta theta past field).length epsilon ≤
        6 * SparseMW.fieldUpdateCount selected past field + leafPrecision epsilon * (3 + offsetWidth (caps field)) :=
  scheduledPrefixBitBudget_bound _ _ _ epsilon
    (resourceBlockHistory_length caps decode selected opponent eta theta past field)

theorem fieldUpdateCount_le_length {a m : ℕ} (selected : List (Fin a) → Fin a → Fin m)
    (past : List (Fin a)) (field : Fin m) : SparseMW.fieldUpdateCount selected past field ≤ past.length := by
  induction past with
  | nil => simp [SparseMW.fieldUpdateCount]
  | cons x past ih =>
    simp only [SparseMW.fieldUpdateCount, List.length_cons]
    split <;> omega

theorem resourceBlockHistory_horizon_leafBitBudget {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta epsilon : ℚ) (past : List (Fin a)) (field : Fin m) (T : ℕ) (hT : past.length ≤ T) :
    scheduledPrefixBitBudget (caps field)
      (resourceBlockHistory caps decode selected opponent eta theta past field).length epsilon ≤
        6 * T + leafPrecision epsilon * (3 + offsetWidth (caps field)) := by
  have hb := resourceBlockHistory_leafBitBudget caps decode selected opponent eta theta epsilon past field
  have hc := (fieldUpdateCount_le_length selected past field).trans hT
  omega

theorem resourceBlockHistory_horizon_word_cap {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta epsilon : ℚ) (he : 0 < epsilon) (past : List (Fin a)) (field : Fin m)
    (T : ℕ) (hT : past.length ≤ T) :
    scheduledPrefixBitBudget (caps field)
      (resourceBlockHistory caps decode selected opponent eta theta past field).length epsilon ≤
        6 * T + (6 + binaryWordWidth (16 * epsilon).den) * (3 + offsetWidth (caps field)) := by
  have hb := resourceBlockHistory_horizon_leafBitBudget caps decode selected opponent eta theta epsilon past field T hT
  exact hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (leafPrecision_denominator_width epsilon he)) _)

end Blotto.ImplicitLeafCounts
