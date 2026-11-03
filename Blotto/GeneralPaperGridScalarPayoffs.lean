import Blotto.GeneralPaperAlgorithmContract

/-! Exact scalar payoffs of the two-field grid counterexample, with the
canonical half-tie convention and arbitrary continuous rich deviations. -/
namespace Blotto.GeneralPaperGridScalarPayoffs
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

noncomputable def pair (own t opposing u : ℝ) : ℝ :=
  (share t u + share (own-t) (opposing-u)) / 2
noncomputable def richMean (q t : ℝ) : ℝ :=
  (pair (3*q) t (2*q) 0 + pair (3*q) t (2*q) q + pair (3*q) t (2*q) (2*q)) / 3
noncomputable def poorMean (q y : ℝ) : ℝ :=
  pair (2*q) y (3*q) (q-1) / 3 + pair (2*q) y (3*q) (q+1) / 6 +
    pair (2*q) y (3*q) (2*q) / 3 + pair (2*q) y (3*q) (2*q+1) / 6

theorem share_reverse (B s t : ℝ) : share (B-s) (B-t) = share t s := by
  simp only [share, sub_lt_sub_iff_left, sub_right_inj, eq_comm]

theorem rich_pair (q t u : ℝ) : pair (3*q) t (2*q) u =
    (share t u + 1 - share t (q+u)) / 2 := by
  have he : 2*q-u = 3*q-(q+u) := by ring
  have hc := share_constant_sum (q+u) t
  unfold pair
  rw [he, share_reverse]
  linarith

theorem rich_formula (q t : ℝ) : richMean q t = 1/2 + (share t 0 - share t (3*q)) / 6 := by
  unfold richMean
  rw [rich_pair, rich_pair, rich_pair]
  rw [add_zero, show q+q = 2*q by ring, show q+2*q = 3*q by ring]
  ring

theorem rich_bound (q t : ℝ) : richMean q t ≤ 2/3 := by
  rw [rich_formula]
  have h0 := share_le_one t 0
  have h3 := share_nonneg t (3*q)
  linarith

theorem share_losing (s t : ℝ) (h : s < t) : share s t = 0 := by
  simp [share, not_lt_of_ge h.le, ne_of_lt h]

theorem share_winning (s t : ℝ) (h : t < s) : share s t = 1 := by
  simp [share, h]

theorem rich_interior (q t : ℝ) (h0 : 0 < t) (h3 : t < 3*q) : richMean q t = 2/3 := by
  rw [rich_formula, share_winning _ _ h0, share_losing _ _ h3]
  norm_num

theorem pair_poor_bound (own opposing t u : ℝ) (hB : own < opposing) : pair own t opposing u ≤ 1/2 := by
  rcases lt_trichotomy t u with h | h | h
  · have hz : share t u = 0 := by simp [share, not_lt_of_ge h.le, ne_of_lt h]
    have hs := share_le_one (own-t) (opposing-u)
    unfold pair
    rw [hz]
    linarith
  · subst u
    have hs : own-t < opposing-t := by linarith
    rw [pair, share_tie, share_losing _ _ hs]
    norm_num
  · have hs : own-t < opposing-u := by linarith
    rw [pair, share_winning _ _ h, share_losing _ _ hs]
    norm_num

theorem poor_low (q y : ℝ) (_hq : 0 < q) (hy : 0 ≤ y) (hyq : y ≤ q-2) : poorMean q y ≤ 1/3 := by
  have hz : pair (2*q) y (3*q) (q-1) = 0 := by
    rw [pair, share_losing _ _ (by linarith), share_losing _ _ (by linarith)]
    norm_num
  have h1 := pair_poor_bound (2*q) (3*q) y (q+1) (by linarith)
  have h2 := pair_poor_bound (2*q) (3*q) y (2*q) (by linarith)
  have h3 := pair_poor_bound (2*q) (3*q) y (2*q+1) (by linarith)
  unfold poorMean
  rw [hz]
  linarith

theorem poor_middle (q y : ℝ) (_hq : 0 < q) (hy : q+1 ≤ y) (hyq : y ≤ 2*q-1) : poorMean q y ≤ 1/3 := by
  have hz : pair (2*q) y (3*q) (2*q) = 0 := by
    rw [pair, share_losing _ _ (by linarith), share_losing _ _ (by linarith)]
    norm_num
  have h0 := pair_poor_bound (2*q) (3*q) y (q-1) (by linarith)
  have h1 := pair_poor_bound (2*q) (3*q) y (q+1) (by linarith)
  have h3 := pair_poor_bound (2*q) (3*q) y (2*q+1) (by linarith)
  unfold poorMean
  rw [hz]
  linarith

theorem poor_boundaries (q : ℝ) (hq : 3 ≤ q) :
    poorMean q (q-1) = 1/3 ∧ poorMean q q = 1/3 ∧ poorMean q (2*q) = 1/3 := by
  constructor
  · simp only [poorMean, pair, share]
    repeat' (split <;> (try linarith))
    all_goals (ring_nf at *; simp_all)
  · constructor
    · simp only [poorMean, pair, share]
      repeat' (split <;> (try linarith))
      all_goals (ring_nf at *; simp_all)
    · simp only [poorMean, pair, share]
      repeat' (split <;> (try linarith))
      all_goals (ring_nf at *; simp_all)

theorem poor_off_grid (q : ℝ) (hq : 3 ≤ q) : poorMean q (q-1/2) = 5/12 := by
  simp only [poorMean, pair, share]
  repeat' (split <;> (try linarith))

end Blotto.GeneralPaperGridScalarPayoffs
