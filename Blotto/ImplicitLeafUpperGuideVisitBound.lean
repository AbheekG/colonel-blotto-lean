import Blotto.ImplicitLeafUpperGuideSize
import Blotto.ImplicitLeafUpperGuideWork

/-! Generated rounded histories give logarithmic implicit upper-guide query
counts. This joins the actual constructor, bin-size theorem and sparse block
growth; predicate/decoder arithmetic and binary cost remain separate. -/

namespace Blotto.ImplicitLeafCounts

theorem upperBinsWithVisits_log_bound (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) :
    ((upperBinsWithVisits C blocks decode (1 + delta) 0).2 : ℝ) ≤
      (1 + 2 * Real.log ((totalMass blocks : ℝ) / (plateauPrefix C blocks decode 0 : ℝ)) / (delta : ℝ)) *
        ((2 * binaryWordWidth (C + 1) + 5 * blocks.length : ℕ) : ℝ) := by
  have hVisits := upperBinsWithVisits_bound C blocks hp hw decode hm (1 + delta) (by linarith) 0
  have hSize := upperGuide_length_log_bound C blocks hp hw decode hm delta hd hu
  have hLength : (upperGuide C blocks decode (1 + delta)).length =
      (upperBins C blocks decode (1 + delta) 0).length := List.length_map _
  rw [hLength] at hSize
  have hvR : ((upperBinsWithVisits C blocks decode (1 + delta) 0).2 : ℝ) ≤
      ((upperBins C blocks decode (1 + delta) 0).length : ℝ) *
        ((2 * binaryWordWidth (C + 1) + 5 * blocks.length : ℕ) : ℝ) := by exact_mod_cast hVisits
  exact hvR.trans (mul_le_mul_of_nonneg_right hSize (by positivity))

theorem resourceBlockHistory_upperGuide_visits {a m : ℕ} (caps : Fin m → ℕ) (decode : Fin m → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (selected : List (Fin a) → Fin a → Fin m) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (field : Fin m) (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) :
    ((upperBinsWithVisits (caps field) (resourceBlockHistory caps decode selected opponent eta theta past field)
      (decode field) (1 + delta) 0).2 : ℝ) ≤
      (1 + 2 * (Real.log ((caps field + 1 : ℕ) : ℝ) +
        (SparseMW.fieldUpdateCount selected past field : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ))) / (delta : ℝ)) *
      ((2 * binaryWordWidth (caps field + 1) + 5 * (1 + 2 * SparseMW.fieldUpdateCount selected past field) : ℕ) : ℝ) := by
  let blocks := resourceBlockHistory caps decode selected opponent eta theta past field
  have hp := resourceBlockHistory_partition caps decode selected opponent eta theta past field
  have hw := resourceBlockHistory_positive caps decode selected opponent eta theta heta htheta past field
  have hVisits := upperBinsWithVisits_bound (caps field) blocks hp hw (decode field) (hm field)
    (1 + delta) (by linarith) 0
  have hSize := resourceBlockHistory_upperGuide_length caps decode hm selected opponent eta theta heta htheta
    past field delta hd hu
  have hLength : (upperGuide (caps field) blocks (decode field) (1 + delta)).length =
      (upperBins (caps field) blocks (decode field) (1 + delta) 0).length := List.length_map _
  change ((upperGuide (caps field) blocks (decode field) (1 + delta)).length : ℝ) ≤ _ at hSize
  rw [hLength] at hSize
  have hBlocks := resourceBlockHistory_length caps decode selected opponent eta theta past field
  change blocks.length ≤ 1 + 2 * SparseMW.fieldUpdateCount selected past field at hBlocks
  have hFactor : (2 * binaryWordWidth (caps field + 1) + 5 * blocks.length : ℕ) ≤
      2 * binaryWordWidth (caps field + 1) + 5 * (1 + 2 * SparseMW.fieldUpdateCount selected past field) := by omega
  have hFactorR : ((2 * binaryWordWidth (caps field + 1) + 5 * blocks.length : ℕ) : ℝ) ≤
      ((2 * binaryWordWidth (caps field + 1) + 5 * (1 + 2 * SparseMW.fieldUpdateCount selected past field) : ℕ) : ℝ) := by
    exact_mod_cast hFactor
  have hSizeNonnegative : 0 ≤ 1 + 2 * (Real.log ((caps field + 1 : ℕ) : ℝ) +
      (SparseMW.fieldUpdateCount selected past field : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ))) / (delta : ℝ) :=
    (Nat.cast_nonneg _).trans hSize
  have hVisitsR : ((upperBinsWithVisits (caps field) blocks (decode field) (1 + delta) 0).2 : ℝ) ≤
      ((upperBins (caps field) blocks (decode field) (1 + delta) 0).length : ℝ) *
        ((2 * binaryWordWidth (caps field + 1) + 5 * blocks.length : ℕ) : ℝ) := by exact_mod_cast hVisits
  exact hVisitsR.trans ((mul_le_mul_of_nonneg_right hSize (by positivity)).trans
    (mul_le_mul_of_nonneg_left hFactorR hSizeNonnegative))

end Blotto.ImplicitLeafCounts
