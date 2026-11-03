import Blotto.GeneralPaperEqualCategoricalIntegerData

/-! A cumulative integer-count categorical selector. It skips zero-count
entries and descends once per stored label; it never expands the denominator
range into a table. Its exact uniform-rank mean is the rational mixture. -/
namespace Blotto.GeneralPaperEqualCategoricalSelector
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000
open GeneralPaperEqualCategoricalIntegerData

def select : {k : ℕ} → (c : Fin k → ℕ) → Fin (∑ j, c j) → Fin k
  | 0, c, r => False.elim (by simpa using r.isLt)
  | k + 1, c, r =>
    if h : r.val < c 0 then 0 else
      (select (fun j => c j.succ) ⟨r.val - c 0, by
        have hr : r.val < c 0 + ∑ j : Fin k, c j.succ := by
          simpa only [Fin.sum_univ_succ] using r.isLt
        omega⟩).succ

theorem select_left {k : ℕ} (c : Fin (k + 1) → ℕ) (r : Fin (c 0)) :
    select c ((r.castAdd (∑ j : Fin k, c j.succ)).cast (Fin.sum_univ_succ c).symm) = 0 := by
  rw [select]
  exact dite_eq_left r.isLt

theorem select_right {k : ℕ} (c : Fin (k + 1) → ℕ) (r : Fin (∑ j : Fin k, c j.succ)) :
    select c ((r.natAdd (c 0)).cast (Fin.sum_univ_succ c).symm) =
      (select (fun j => c j.succ) r).succ := by
  rw [select, dite_eq_right (by change ¬c 0 + r.val < c 0; omega)]
  congr 2
  apply Fin.ext
  change c 0 + r.val - c 0 = r.val
  omega

theorem sum_select {k : ℕ} (c : Fin k → ℕ) (f : Fin k → ℝ) :
    (∑ r : Fin (∑ j, c j), f (select c r)) = ∑ j, (c j : ℝ) * f j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := Fin.sum_univ_succ c
    calc
      _ = ∑ r : Fin (c 0 + ∑ j : Fin k, c j.succ),
          f (select c (r.cast hs.symm)) :=
        (Equiv.sum_comp (finCongr hs.symm) (fun r => f (select c r))).symm
      _ = (∑ _r : Fin (c 0), f 0) +
          ∑ r : Fin (∑ j : Fin k, c j.succ), f ((select (fun j => c j.succ) r).succ) := by
        rw [Fin.sum_univ_add]
        simp_rw [select_left, select_right]
      _ = ∑ j, (c j : ℝ) * f j := by
        rw [ih (fun j => c j.succ) (fun j => f j.succ)]
        simp [Fin.sum_univ_succ]

def rank {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (hm : ∑ j, weight j = 1) (r : Fin (denominator weight)) : Fin k :=
  select (count weight) (r.cast (count_sum weight hw hm).symm)

theorem rank_mean {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (hm : ∑ j, weight j = 1) (f : Fin k → ℝ) :
    (UniformNatRejection.targetKernel (denominator weight) (denominator_pos weight)).mean
      (fun r => f (rank weight hw hm r)) = ∑ j, (weight j : ℝ) * f j := by
  change (1 / (denominator weight : ℝ)) * (∑ r, f (rank weight hw hm r)) = _
  have he : (∑ r, f (rank weight hw hm r)) = ∑ j, (count weight j : ℝ) * f j := by
    unfold rank
    have hs := Equiv.sum_comp (finCongr (count_sum weight hw hm).symm)
      (fun r => f (select (count weight) r))
    exact hs.trans (sum_select (count weight) f)
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hq := congrArg (fun q : ℚ => (q : ℝ)) (count_ratio weight hw j)
  simp only [Rat.cast_div, Rat.cast_natCast] at hq
  rw [← hq]
  ring

def run {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (hm : ∑ j, weight j = 1) (cap : ℕ)
    (fresh : Fin (cap * UniformNatRejection.width (denominator weight)) → Bool) : Option (Fin k) :=
  (UniformNatRejection.run (denominator weight) cap fresh).map (rank weight hw hm)

theorem run_mean {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (hm : ∑ j, weight j = 1) (cap : ℕ) (f : Option (Fin k) → ℝ) :
    (fairBitKernel (cap * UniformNatRejection.width (denominator weight))).mean
      (fun fresh => f (run weight hw hm cap fresh)) =
      (1 - rejectionFailure (UniformNatRejection.acceptance (denominator weight) : ℝ) cap) *
        (∑ j, (weight j : ℝ) * f (some j)) +
      rejectionFailure (UniformNatRejection.acceptance (denominator weight) : ℝ) cap * f none := by
  unfold run
  rw [UniformNatRejection.run_mean (denominator weight) cap
    (fun result => f (result.map (rank weight hw hm)))]
  rw [BoundedExpectationKernel.firstSuccess_target_mean _ _ _
    (UniformNatRejection.attemptKernel_mean _ (denominator_pos weight))]
  simp only [Option.map_some, Option.map_none]
  rw [rank_mean weight hw hm (fun j => f (some j))]

theorem mean_tends_exact {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (hm : ∑ j, weight j = 1) (f : Option (Fin k) → ℝ) :
    Filter.Tendsto (fun cap =>
      (fairBitKernel (cap * UniformNatRejection.width (denominator weight))).mean
        (fun fresh => f (run weight hw hm cap fresh))) Filter.atTop
      (nhds (∑ j, (weight j : ℝ) * f (some j))) := by
  simp_rw [run_mean]
  have hf := failure_tends_zero (denominator weight) (denominator_pos weight)
  simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub hf).mul_const
    (∑ j, (weight j : ℝ) * f (some j))).add (hf.mul_const (f none))

theorem failure {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ j, 0 ≤ weight j)
    (hm : ∑ j, weight j = 1) (cap : ℕ) :
    (fairBitKernel (cap * UniformNatRejection.width (denominator weight))).mean
      (fun fresh => if run weight hw hm cap fresh = none then 1 else 0) ≤ 1 / (2 : ℝ) ^ cap := by
  simp only [run, Option.map_eq_none_iff]
  rw [UniformNatRejection.run_failure_mass _ (denominator_pos weight)]
  exact UniformNatRejection.failure_tail _ (denominator_pos weight) cap

end Blotto.GeneralPaperEqualCategoricalSelector
