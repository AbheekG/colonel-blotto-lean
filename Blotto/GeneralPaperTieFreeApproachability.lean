import Blotto.GeneralPaperTieFreeSelector
import Blotto.RichSmoothingCDF

/-! The pure tie-free selectors from the smoothing laws can be chosen
arbitrarily close to the original full-budget allocation. -/
namespace Blotto.GeneralPaperTieFreeApproachability
open MeasureTheory Filter RichSmoothingGeometry RichSmoothingLaw RichSmoothingCDF
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem lower_tendsto {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (j : Fin n) :
    Tendsto (fun k => lower x h (step x h k) j) atTop (𝓝 (x j)) := by
  have hc : Continuous (fun t : ℝ => lower x h t j) := by
    change Continuous (fun t : ℝ => x j-t*direction x h j-t^2*correction x j)
    fun_prop
  have h0 : lower x h 0 j=x j := by simp [lower]
  simpa only [Function.comp_def,h0] using hc.continuousAt.tendsto.comp (step_tendsto x h)

theorem upper_tendsto {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (j : Fin n) :
    Tendsto (fun k => upper x h (step x h k) j) atTop (𝓝 (x j)) := by
  have hc : Continuous (fun t : ℝ => upper x h t j) := by
    change Continuous (fun t : ℝ => x j+t*direction x h j-3*t^2*correction x j)
    fun_prop
  have h0 : upper x h 0 j=x j := by simp [upper]
  simpa only [Function.comp_def,h0] using hc.continuousAt.tendsto.comp (step_tendsto x h)

theorem eventually_endpoint_near {n : ℕ} (x : Allocation n)
    (h : (active x).Nonempty) (r : ℝ) (hr : 0<r) :
    ∀ᶠ k : ℕ in atTop, ∀ j,
      |lower x h (step x h k) j-x j|<r ∧
      |upper x h (step x h k) j-x j|<r := by
  apply Filter.eventually_all.2
  intro j
  have hl : Tendsto (fun k => |lower x h (step x h k) j-x j|)
      atTop (𝓝 (0:ℝ)) := by
    simpa using ((lower_tendsto x h j).sub_const (x j)).abs
  have hu : Tendsto (fun k => |upper x h (step x h k) j-x j|)
      atTop (𝓝 (0:ℝ)) := by
    simpa using ((upper_tendsto x h j).sub_const (x j)).abs
  exact (hl.eventually (isOpen_Iio.mem_nhds hr)).and
    (hu.eventually (isOpen_Iio.mem_nhds hr))

theorem segment_near {n : ℕ} (x P Q : Allocation n) (r u : ℝ)
    (_hr : 0<r) (hu : 0≤u ∧ u≤1)
    (hP : ∀ j, |P j-x j|<r) (hQ : ∀ j, |Q j-x j|<r) :
    ∀ j, |segmentPoint P Q u j-x j|<r := by
  intro j
  have h1 : 0≤1-u := by linarith
  have hp := hP j
  have hq := hQ j
  have heq : segmentPoint P Q u j-x j=(1-u)*(P j-x j)+u*(Q j-x j) := by
    simp [segmentPoint]
    ring
  rw [heq]
  calc
    |(1-u)*(P j-x j)+u*(Q j-x j)|
      ≤ |(1-u)*(P j-x j)|+|u*(Q j-x j)| := abs_add_le _ _
    _ = (1-u)*|P j-x j|+u*|Q j-x j| := by
      rw [abs_mul,abs_mul,abs_of_nonneg h1,abs_of_nonneg hu.1]
    _ < (1-u)*r+u*r := by
      by_cases hzero : u=0
      · subst u
        simpa using hp
      · have hupos : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hzero)
        have hp' := mul_le_mul_of_nonneg_left hp.le h1
        have hq' := mul_lt_mul_of_pos_left hq hupos
        linarith
    _ = r := by ring

theorem law_ae_near {n : ℕ} (x : Allocation n)
    (h : (active x).Nonempty) (r : ℝ) (hr : 0<r) (k : ℕ)
    (hk : ∀ j,
      |lower x h (step x h k) j-x j|<r ∧
      |upper x h (step x h k) j-x j|<r) :
    ∀ᵐ row ∂(law x h (step x h k) : Measure (Allocation n)),
      ∀ j, |row j-x j|<r := by
  have hm : MeasurableSet {row : Allocation n | ∀ j, |row j-x j|<r} := by
    have hj (j : Fin n) : MeasurableSet {row : Allocation n | |row j-x j|<r} := by
      have hf : Measurable (fun row : Allocation n => row j-x j) :=
        (measurable_pi_apply j).sub measurable_const
      exact measurableSet_lt (continuous_abs.measurable.comp hf) measurable_const
    simpa only [Set.ofPred_forall] using MeasurableSet.iInter hj
  change ∀ᵐ row ∂Measure.map
      (segmentPoint (lower x h (step x h k)) (upper x h (step x h k)))
      (unitUniform : Measure ℝ), ∀ j, |row j-x j|<r
  apply (ae_map_iff (measurable_segmentPoint _ _).aemeasurable hm).mpr
  apply unitUniform_supported.mono
  intro u hu
  exact segment_near x _ _ r u hr hu (fun j => (hk j).1) (fun j => (hk j).2)

theorem exists_tie_free_above_average_near {n : ℕ} (values : Values n)
    (x : Allocation n) (r : ℝ) {budget : ℝ} (smooth opponent : Mixed n)
    (hRegular : Regular budget smooth)
    (hNear : ∀ᵐ row ∂(smooth : Measure (Allocation n)), ∀ j, |row j-x j|<r)
    (epsilon : ℝ) (he : 0<epsilon) :
    ∃ x' : Allocation n, FullBudget budget x' ∧
      GeneralPaperTieFreeSelector.TieFree x' opponent ∧
      (∀ j, |x' j-x j|<r) ∧
      expected values smooth opponent-epsilon < purePayoff values x' opponent := by
  have hgood : ∀ᵐ row ∂(smooth : Measure (Allocation n)),
      FullBudget budget row ∧ GeneralPaperTieFreeSelector.TieFree row opponent ∧
      (∀ j, |row j-x j|<r) := by
    filter_upwards [hRegular.1,
      GeneralPaperTieFreeSelector.tie_free_ae smooth opponent
        (GeneralPaperAtomlessRegularTransfer.rich_regular_atomless hRegular),hNear]
      with row hf ht hn
    exact ⟨hf.1,ht,hn⟩
  by_contra hnone
  have hpoint : ∀ᵐ row ∂(smooth : Measure (Allocation n)),
      purePayoff values row opponent≤expected values smooth opponent-epsilon := by
    filter_upwards [hgood] with row hrow
    exact le_of_not_gt (fun hgt => hnone ⟨row,hrow.1,hrow.2.1,hrow.2.2,hgt⟩)
  have hIntegral := integral_mono_ae
    (integrable_purePayoff values smooth opponent)
    (integrable_const (expected values smooth opponent-epsilon)) hpoint
  rw [←expected_iterated] at hIntegral
  simp at hIntegral
  linarith

theorem exists_tie_free_local_approach {n : ℕ} (values : Values n)
    (x : Allocation n) {A B : ℝ} (hA : 0<A) (hX : FullBudget A x)
    (hn : 2≤n) (hBudgets : B<A)
    (opponent : Mixed n) (hOpponent : Supported B opponent)
    (epsilon r : ℝ) (he : 0<epsilon) (hr : 0<r) :
    ∃ x' : Allocation n, FullBudget A x' ∧
      GeneralPaperTieFreeSelector.TieFree x' opponent ∧
      (∀ j, |x' j-x j|<r) ∧
      purePayoff values x opponent-epsilon < purePayoff values x' opponent := by
  let h := active_nonempty x A hA hX
  let L := ∫ y, RichSmoothingApproximation.limitPayoff values x y
    ∂(opponent : Measure (Allocation n))
  have hhalf : 0<epsilon/2 := by linarith
  have hLimit := RichSmoothingApproximation.expected_limit
    values x hA hX hn hBudgets opponent hOpponent
  have hPayoff := hLimit.eventually_lt_const (show L<L+epsilon/2 by linarith)
  have hNear := eventually_endpoint_near x h r hr
  obtain ⟨k,hk,hkn⟩ := (hPayoff.and hNear).exists
  let smooth := law x h (step x h k)
  have hRegular : Regular A smooth :=
    law_regular x A hA hX hn _ (step_positive x h k) (step_le_radius x h k)
  obtain ⟨x',hFull,hTie,hCoordinate,hGood⟩ :=
    exists_tie_free_above_average_near values x r smooth opponent hRegular
      (law_ae_near x h r hr k hkn) (epsilon/2) hhalf
  refine ⟨x',hFull,hTie,hCoordinate,?_⟩
  have hBound := RichSmoothingApproximation.limit_integral_le values x opponent
  have hSum := expected_constant_sum values smooth opponent
  change expected values opponent smooth<L+epsilon/2 at hk
  change L≤1-purePayoff values x opponent at hBound
  linarith

end Blotto.GeneralPaperTieFreeApproachability
