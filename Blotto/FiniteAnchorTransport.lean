import Blotto.Mixed

/-! A Borel relabelling of a finite scalar catalogue. Duplicate source
anchors cause no selection problem: average all their target labels. When
equal source anchors have equal targets, the average is that exact target.
No inverse, measurable selector or probability weights are supplied. -/

namespace Blotto.FiniteAnchorTransport
open MeasureTheory
open scoped BigOperators Classical

noncomputable def hit {ι : Type*} (old : ι → ℝ) (i : ι) (x : ℝ) : ℝ :=
  if x = old i then 1 else 0

noncomputable def mass {ι : Type*} [Fintype ι] (old : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, hit old i x

noncomputable def weighted {ι : Type*} [Fintype ι] (old target : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, target i * hit old i x

noncomputable def relabel {ι : Type*} [Fintype ι] (old target : ι → ℝ) (x : ℝ) : ℝ :=
  weighted old target x / mass old x

theorem hit_measurable {ι : Type*} (old : ι → ℝ) (i : ι) :
    Measurable (hit old i) := by
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
    measurable_const measurable_const

theorem relabel_measurable {ι : Type*} [Fintype ι] (old target : ι → ℝ) :
    Measurable (relabel old target) := by
  unfold relabel weighted mass
  exact (Finset.measurable_sum _ (fun i _ => measurable_const.mul (hit_measurable old i))).div
    (Finset.measurable_sum _ (fun i _ => hit_measurable old i))

theorem hit_nonnegative {ι : Type*} (old : ι → ℝ) (i : ι) (x : ℝ) :
    0 ≤ hit old i x := by
  unfold hit
  split_ifs <;> norm_num

theorem mass_positive_at_anchor {ι : Type*} [Fintype ι] (old : ι → ℝ) (j : ι) :
    0 < mass old (old j) := by
  have h : hit old j (old j) ≤ mass old (old j) :=
    Finset.single_le_sum (fun i _ => hit_nonnegative old i (old j)) (Finset.mem_univ j)
  simpa [hit] using lt_of_lt_of_le (by simp [hit] : (0 : ℝ) < hit old j (old j)) h

theorem relabel_at_anchor {ι : Type*} [Fintype ι] (old target : ι → ℝ)
    (hDuplicates : ∀ i j, old i = old j → target i = target j) (j : ι) :
    relabel old target (old j) = target j := by
  have hWeighted : weighted old target (old j) = target j * mass old (old j) := by
    unfold weighted mass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : old j = old i
    · rw [hDuplicates i j h.symm]
    · simp [hit,h]
  unfold relabel
  rw [hWeighted]
  exact mul_div_cancel_right₀ _ (ne_of_gt (mass_positive_at_anchor old j))

end Blotto.FiniteAnchorTransport
