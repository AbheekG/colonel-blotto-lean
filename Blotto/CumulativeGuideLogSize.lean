import Blotto.CumulativeGuideSize
import Blotto.AdaptiveRoundedFieldHistory

/-! Logarithmic retained-guide size. The first retained positive height remains
explicit; a source-specific lower bound on it is a separate construction
obligation. Unlike the Bernoulli envelope, these bounds depend on the logarithm
of the mass ratio, so exponentially small weights do not cause exponential size. -/

namespace Blotto.CumulativeGuidePruning

theorem log_one_add_lower {delta : ℝ} (hd : 0 ≤ delta) (hu : delta ≤ 1) :
    delta / 2 ≤ Real.log (1 + delta) := by
  have hp : 0 < 1 + delta := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have he : 1 - (1 + delta)⁻¹ = delta / (1 + delta) := by
    field_simp
    ring
  rw [he] at hlog
  have hdiv : delta / 2 ≤ delta / (1 + delta) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  exact hdiv.trans hlog

theorem geometric_log_bound {gamma first total : ℝ} (n : ℕ)
    (hg : 0 < gamma) (hf : 0 < first) (hpow : gamma ^ n * first ≤ total) :
    (n : ℝ) * Real.log gamma ≤ Real.log (total / first) := by
  have hp : 0 < gamma ^ n * first := mul_pos (pow_pos hg _) hf
  have ht : 0 < total := hp.trans_le hpow
  have hlog := Real.log_le_log hp hpow
  rw [Real.log_mul (pow_ne_zero _ hg.ne') hf.ne', Real.log_pow] at hlog
  rw [Real.log_div ht.ne' hf.ne']
  linarith

theorem geometric_delta_log_bound {delta first total : ℝ} (n : ℕ)
    (hd : 0 < delta) (hu : delta ≤ 1) (hf : 0 < first)
    (hpow : (1 + delta) ^ n * first ≤ total) :
    (n : ℝ) * delta ≤ 2 * Real.log (total / first) := by
  have hlog := geometric_log_bound n (by linarith : 0 < 1 + delta) hf hpow
  have hlow := mul_le_mul_of_nonneg_left (log_one_add_lower hd.le hu)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

theorem prune_delta_log_count_bound (atoms : List Atom) (delta : ℚ)
    (hd : 0 < delta) (hu : delta ≤ 1) (h : Nonnegative atoms)
    (first : ℚ) (rest : List ℚ)
    (heights : cumulativeHeights (prune (1 + delta) atoms) 0 = first :: rest) :
    (((prune (1 + delta) atoms).length - 1 : ℕ) : ℝ) * (delta : ℝ) ≤
      2 * Real.log ((totalMass atoms : ℝ) / (first : ℝ)) := by
  have hp := prune_size_power_bound atoms (1 + delta) (by linarith) h first rest heights
  have hf : (0 : ℝ) < first := by exact_mod_cast hp.1
  have hpow : (1 + (delta : ℝ)) ^ ((prune (1 + delta) atoms).length - 1) * (first : ℝ) ≤
      (totalMass atoms : ℝ) := by exact_mod_cast hp.2
  exact geometric_delta_log_bound _ (by exact_mod_cast hd) (by exact_mod_cast hu) hf hpow

theorem prune_length_log_bound (atoms : List Atom) (delta : ℚ)
    (hd : 0 < delta) (hu : delta ≤ 1) (h : Nonnegative atoms)
    (first : ℚ) (rest : List ℚ)
    (heights : cumulativeHeights (prune (1 + delta) atoms) 0 = first :: rest) :
    ((prune (1 + delta) atoms).length : ℝ) ≤
      1 + 2 * Real.log ((totalMass atoms : ℝ) / (first : ℝ)) / (delta : ℝ) := by
  have hb := prune_delta_log_count_bound atoms delta hd hu h first rest heights
  have hl : (prune (1 + delta) atoms).length = rest.length + 1 := by
    have he := cumulativeHeights_length (prune (1 + delta) atoms) 0
    rw [heights, List.length_cons] at he
    exact he.symm
  have hdR : (0 : ℝ) < delta := by exact_mod_cast hd
  have hdiv := (le_div_iff₀ hdR).mpr hb
  rw [hl, Nat.add_sub_cancel] at hdiv
  rw [hl, Nat.cast_add, Nat.cast_one]
  linarith

theorem prune_length_exp_range_bound (atoms : List Atom) (delta : ℚ)
    (hd : 0 < delta) (hu : delta ≤ 1) (h : Nonnegative atoms)
    (first : ℚ) (rest : List ℚ)
    (heights : cumulativeHeights (prune (1 + delta) atoms) 0 = first :: rest)
    (range : ℝ) (hr : (totalMass atoms : ℝ) / (first : ℝ) ≤ Real.exp range) :
    ((prune (1 + delta) atoms).length : ℝ) ≤ 1 + 2 * range / (delta : ℝ) := by
  have hp := prune_size_power_bound atoms (1 + delta) (by linarith) h first rest heights
  have hf : (0 : ℝ) < first := by exact_mod_cast hp.1
  have hg : (0 : ℝ) < 1 + (delta : ℝ) := by exact_mod_cast (by linarith : (0 : ℚ) < 1 + delta)
  have hpow : (1 + (delta : ℝ)) ^ ((prune (1 + delta) atoms).length - 1) * (first : ℝ) ≤
      (totalMass atoms : ℝ) := by exact_mod_cast hp.2
  have ht := (mul_pos (pow_pos hg _) hf).trans_le hpow
  have hlog := Real.log_le_log (div_pos ht hf) hr
  rw [Real.log_exp] at hlog
  have hdR : (0 : ℝ) < delta := by exact_mod_cast hd
  exact (prune_length_log_bound atoms delta hd hu h first rest heights).trans
    (add_le_add_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2)) hdR.le) 1)

end Blotto.CumulativeGuidePruning
