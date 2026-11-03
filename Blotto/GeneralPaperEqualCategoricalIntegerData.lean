import Blotto.UniformNatRejection
import Blotto.RationalLotteryHeight
import Mathlib.Analysis.SpecificLimits.Basic

/-! Fixed-size rational categorical probabilities compile to integer counts
over one derived common denominator. Uniform integer rejection has a
geometric failure tail and uniformly bounded expected fair-bit charge at
every finite truncation. The cumulative count selector and its sampling-law
join are separate from these integer data and rejection estimates. -/
namespace Blotto.GeneralPaperEqualCategoricalIntegerData
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 500000

def denominator {k : ℕ} (weight : Fin k → ℚ) : ℕ := ∏ j, (weight j).den

def count {k : ℕ} (weight : Fin k → ℚ) (j : Fin k) : ℕ :=
  (weight j).num.toNat * (denominator weight / (weight j).den)

theorem denominator_pos {k : ℕ} (weight : Fin k → ℚ) : 0 < denominator weight :=
  Finset.prod_pos (fun j _ => (weight j).den_pos)

theorem denominator_multiple {k : ℕ} (weight : Fin k → ℚ) (j : Fin k) :
    (weight j).den ∣ denominator weight :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

theorem scaled_count {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j) (j : Fin k) :
    (denominator weight : ℚ) * weight j = (count weight j : ℚ) := by
  have hn : 0 ≤ (weight j).num := Rat.num_nonneg.mpr (hw j)
  have hnum : ((weight j).num.toNat : ℚ) = ((weight j).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  have hd := Nat.mul_div_cancel' (denominator_multiple weight j)
  have hq : ((weight j).den : ℚ) * weight j = (weight j).num := by
    have hden : ((weight j).den : ℚ) ≠ 0 := by exact_mod_cast (weight j).den_pos.ne'
    exact (mul_comm _ _).trans ((div_eq_iff hden).mp (weight j).num_div_den).symm
  calc
    (denominator weight : ℚ) * weight j =
        (((weight j).den * (denominator weight / (weight j).den) : ℕ) : ℚ) * weight j := by rw [hd]
    _ = (denominator weight / (weight j).den : ℕ) *
        (((weight j).den : ℚ) * weight j) := by push_cast; ring
    _ = (count weight j : ℚ) := by rw [hq]; simp only [count, Nat.cast_mul, hnum]; ring

theorem count_sum {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (hm : ∑ j, weight j = 1) : ∑ j, count weight j = denominator weight := by
  have h : ((∑ j, count weight j : ℕ) : ℚ) = (denominator weight : ℚ) := by
    push_cast
    simp_rw [← scaled_count weight hw]
    rw [← Finset.mul_sum, hm, mul_one]
  exact_mod_cast h

theorem count_ratio {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j) (j : Fin k) :
    (count weight j : ℚ) / denominator weight = weight j := by
  rw [← scaled_count weight hw]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (denominator_pos weight).ne')

theorem count_le_denominator {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (hm : ∑ j, weight j = 1) (j : Fin k) : count weight j ≤ denominator weight := by
  rw [← count_sum weight hw hm]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem denominator_height {k s : ℕ} (weight : Fin k → ℚ)
    (h : ∀ j, RationalHeight (weight j) s) : denominator weight ≤ 2 ^ (s * k) := by
  calc
    denominator weight ≤ ∏ _j : Fin k, 2 ^ s :=
      Finset.prod_le_prod (fun j _ => (h j).2.le)
    _ = 2 ^ (s * k) := by simp [← pow_mul]

theorem denominator_word {k s : ℕ} (weight : Fin k → ℚ)
    (h : ∀ j, RationalHeight (weight j) s) :
    binaryWordWidth (denominator weight) ≤ s * k + 1 := by
  have he := binaryWordWidth_mono (denominator_height weight h)
  simpa only [binaryWordWidth, Nat.log2_two_pow] using he

theorem rejection_width {k s : ℕ} (weight : Fin k → ℚ)
    (h : ∀ j, RationalHeight (weight j) s) :
    UniformNatRejection.width (denominator weight) ≤ s * k + 1 := by
  apply widthRatioPrecision_minimal (denominator weight) 1 (s * k + 1)
    (denominator_pos weight) (by decide)
  simpa only [one_mul] using
    (denominator_height weight h).trans (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : s * k ≤ s * k + 1))

theorem expected_attempts (N : ℕ) (hN : 0 < N) (cap : ℕ) :
    rejectionExpectedAttempts (UniformNatRejection.acceptance N : ℝ) cap ≤ 2 := by
  have ha := UniformNatRejection.acceptance_bounds N hN
  have he := rejectionExpectedAttempts_le_inverse (by linarith only [ha.1]) ha.2 cap
  have hi : 1 / (UniformNatRejection.acceptance N : ℝ) ≤ 2 :=
    (div_le_iff₀ (by linarith only [ha.1])).mpr (by linarith only [ha.1])
  exact he.trans hi

theorem expected_fair_bit_charge {k s : ℕ} (weight : Fin k → ℚ)
    (h : ∀ j, RationalHeight (weight j) s) (cap : ℕ) :
    (UniformNatRejection.width (denominator weight) : ℝ) *
      rejectionExpectedAttempts (UniformNatRejection.acceptance (denominator weight) : ℝ) cap ≤
      2 * (s * k + 1 : ℕ) := by
  have he := expected_attempts (denominator weight) (denominator_pos weight) cap
  have hw : (UniformNatRejection.width (denominator weight) : ℝ) ≤ (s * k + 1 : ℕ) := by
    exact_mod_cast rejection_width weight h
  calc
    _ ≤ (UniformNatRejection.width (denominator weight) : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ _ := by nlinarith only [hw]

theorem failure_tends_zero (N : ℕ) (hN : 0 < N) :
    Filter.Tendsto (rejectionFailure (UniformNatRejection.acceptance N : ℝ))
      Filter.atTop (nhds 0) := by
  have ha := UniformNatRejection.acceptance_bounds N hN
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith only [ha.2])
    (by linarith only [ha.1])

end Blotto.GeneralPaperEqualCategoricalIntegerData
