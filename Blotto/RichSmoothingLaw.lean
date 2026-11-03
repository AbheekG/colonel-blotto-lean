import Blotto.RichSmoothingGeometry
import Blotto.FiniteMixture

/-! Actual regular rich laws from the single-scalar smoothing segments.
Every coordinate is positive and atom-free while the whole draw spends the
budget. Regular laws are closed under finite mixing. Their opposing pure
payoff is continuous, so expected payoff is continuous in the opponent's
weak topology. Fixed-opponent approximation and minimax totality remain
separate: weak convergence alone does not transfer discontinuous game payoff. -/

namespace Blotto.RichSmoothingLaw
open MeasureTheory Set Filter ProbabilityTheory Function
open RichSmoothingGeometry
open scoped Topology BigOperators Classical BoundedContinuousFunction

def Regular {n : ℕ} (budget : ℝ) (law : Mixed n) : Prop :=
  (∀ᵐ row ∂(law : Measure (Allocation n)), FullBudget budget row ∧ ∀ j, 0 < row j) ∧
    ∀ j z, (marginal law j : Measure ℝ) {z} = 0

theorem regular_supported {n : ℕ} {budget : ℝ} {law : Mixed n}
    (hLaw : Regular budget law) : Supported budget law :=
  hLaw.1.mono fun _ h => fullBudget_feasible h.1

theorem measurable_positive {n : ℕ} : MeasurableSet {row : Allocation n | ∀ j, 0 < row j} := by
  have h : {row : Allocation n | ∀ j, 0 < row j} = ⋂ j : Fin n, {row | 0 < row j} := by
    ext row; simp
  rw [h]
  exact MeasurableSet.iInter fun j => measurableSet_lt measurable_const (measurable_pi_apply j)

theorem affineUniform_singleton {a b : ℝ} (hab : a ≠ b) (z : ℝ) :
    (affineUniform a b : Measure ℝ) {z} = 0 := by
  have hZero : volume ({z} ∩ Icc (min a b) (max a b)) = 0 := by
    apply le_antisymm _ zero_le
    exact (measure_mono inter_subset_left).trans_eq (measure_singleton z)
  rw [affineUniform_sorted]
  simp [sortedIntervalLaw, hab, intervalLaw, Measure.restrict_apply (measurableSet_singleton z), hZero]

theorem segment_regular {n : ℕ} (budget : ℝ) (P Q : Allocation n)
    (hP : FullBudget budget P) (hQ : FullBudget budget Q)
    (hPositive : ∀ j, 0 < P j ∧ 0 < Q j) (hDistinct : ∀ j, P j ≠ Q j) :
    Regular budget (segmentLaw P Q) := by
  constructor
  · change ∀ᵐ row ∂Measure.map (segmentPoint P Q) (unitUniform : Measure ℝ),
      FullBudget budget row ∧ ∀ j, 0 < row j
    apply (ae_map_iff (measurable_segmentPoint P Q).aemeasurable
      ((measurable_fullBudget budget).inter measurable_positive)).mpr
    apply unitUniform_supported.mono
    intro u hu
    refine ⟨segment_fullBudget hP hQ hu, ?_⟩
    intro j
    change 0 < (1 - u) * P j + u * Q j
    have hFirst := mul_nonneg (sub_nonneg.mpr hu.2) (hPositive j).1.le
    have hSecond := mul_nonneg hu.1 (hPositive j).2.le
    by_cases hZero : u = 0
    · subst u; simpa using (hPositive j).1
    · have hPositiveSecond := mul_pos (lt_of_le_of_ne hu.1 (Ne.symm hZero)) (hPositive j).2
      linarith
  · intro j z
    rw [segmentLaw_marginal]
    exact affineUniform_singleton (hDistinct j) z

noncomputable def law {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) (t : ℝ) : Mixed n :=
  segmentLaw (lower x h t) (upper x h t)

theorem law_regular {n : ℕ} (x : Allocation n) (budget : ℝ)
    (hBudget : 0 < budget) (hX : FullBudget budget x) (hn : 2 ≤ n)
    (t : ℝ) (ht : 0 < t) (htr : t ≤ radius x (active_nonempty x budget hBudget hX)) :
    Regular budget (law x (active_nonempty x budget hBudget hX) t) := by
  have hFull := endpoint_fullBudgets x budget hBudget hX hn t ht htr
  exact segment_regular budget _ _ hFull.1 hFull.2
    (positive_endpoints x _ hn hX.1 t ht htr)
    (distinct_endpoints x _ hn hX.1 t ht htr)

theorem regular_mixture {n k : ℕ} (budget : ℝ) (weights : Fin k → ℝ)
    (laws : Fin k → Mixed n) (hWeights : ∀ i, 0 ≤ weights i) (hSum : ∑ i, weights i = 1)
    (hLaws : ∀ i, Regular budget (laws i)) :
    Regular budget (probabilityMixture weights laws hWeights hSum) := by
  constructor
  · exact probabilityMixture_ae weights laws hWeights hSum fun i => (hLaws i).1
  · intro j z
    rw [probabilityMixture_marginal, Measure.sum_apply _ (measurableSet_singleton z), tsum_fintype]
    simp only [Measure.smul_apply, (hLaws _).2, smul_eq_mul, mul_zero, Finset.sum_const_zero]

theorem atomless_cdf_continuous (rho : ProbabilityMeasure ℝ)
    (hAtoms : ∀ z, (rho : Measure ℝ) {z} = 0) : Continuous (cdf (rho : Measure ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hLeft : leftLim (cdf (rho : Measure ℝ)) z = cdf (rho : Measure ℝ) z := by
    rw [← real_Iio_eq_leftLim, cdf_eq_real]
    unfold Measure.real
    congr 1
    exact measure_congr (Iio_ae_eq_Iic' (hAtoms z))
  have hContinuousLeft : ContinuousWithinAt (cdf (rho : Measure ℝ)) (Iio z) z :=
    ((monotone_cdf (rho : Measure ℝ)).continuousWithinAt_Iio_iff_leftLim_eq).mpr hLeft
  exact continuousAt_iff_continuous_left_right.mpr
    ⟨continuousWithinAt_Iio_iff_Iic.mp hContinuousLeft,
      (cdf (rho : Measure ℝ)).right_continuous z⟩

theorem regular_strict_eq_closed {n : ℕ} {budget : ℝ} {smooth : Mixed n}
    (hSmooth : Regular budget smooth) (j : Fin n) (z : ℝ) :
    strictCDF smooth j z = closedCDF smooth j z := by
  unfold strictCDF closedCDF Measure.real
  congr 1
  exact measure_congr (Iio_ae_eq_Iic' (hSmooth.2 j z))

theorem regular_closedCDF_continuous {n : ℕ} {budget : ℝ} {smooth : Mixed n}
    (hSmooth : Regular budget smooth) (j : Fin n) : Continuous (closedCDF smooth j) := by
  have h : closedCDF smooth j = cdf (marginal smooth j : Measure ℝ) := by
    funext z
    exact (cdf_eq_real _ z).symm
  rw [h]
  exact atomless_cdf_continuous _ (hSmooth.2 j)

theorem regular_purePayoff_continuous {n : ℕ} (values : Values n) {budget : ℝ} {smooth : Mixed n}
    (hSmooth : Regular budget smooth) : Continuous (fun y : Allocation n => purePayoff values y smooth) := by
  have h : (fun y : Allocation n => purePayoff values y smooth) =
      fun y => ∑ j, values.weight j * closedCDF smooth j (y j) := by
    funext y
    rw [purePayoff_marginals]
    apply Finset.sum_congr rfl
    intro j _
    rw [regular_strict_eq_closed hSmooth]
    ring
  rw [h]
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((regular_closedCDF_continuous hSmooth j).comp (continuous_apply j))

noncomputable def opponentPayoff {n : ℕ} (values : Values n) {budget : ℝ} (smooth : Mixed n)
    (hSmooth : Regular budget smooth) : Allocation n →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => purePayoff values y smooth, regular_purePayoff_continuous values hSmooth⟩ 1 (by
      intro first second
      rw [Real.dist_eq]
      change |purePayoff values first smooth - purePayoff values second smooth| ≤ 1
      apply abs_le.mpr
      have hf0 := purePayoff_nonneg values first smooth
      have hf1 := purePayoff_le_one values first smooth
      have hs0 := purePayoff_nonneg values second smooth
      have hs1 := purePayoff_le_one values second smooth
      constructor <;> linarith)

theorem regular_expected_continuous {n : ℕ} (values : Values n) {budget : ℝ} (smooth : Mixed n)
    (hSmooth : Regular budget smooth) : Continuous (fun opponent : Mixed n => expected values opponent smooth) := by
  have h := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (opponentPayoff values smooth hSmooth)
  change Continuous (fun opponent : Mixed n =>
    ∫ row, purePayoff values row smooth ∂(opponent : Measure (Allocation n))) at h
  simpa only [expected_iterated] using h

theorem regular_rich_expected_continuous {n : ℕ} (values : Values n) {budget : ℝ} (smooth : Mixed n)
    (hSmooth : Regular budget smooth) : Continuous (fun opponent : Mixed n => expected values smooth opponent) := by
  have h : (fun opponent : Mixed n => expected values smooth opponent) =
      fun opponent => 1 - expected values opponent smooth := by
    funext opponent
    have hc := expected_constant_sum values smooth opponent
    linarith
  rw [h]
  exact continuous_const.sub (regular_expected_continuous values smooth hSmooth)

end Blotto.RichSmoothingLaw
