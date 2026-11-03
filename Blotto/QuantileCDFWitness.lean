import Blotto.CDF

/-! An actual lower quantile of any real probability law supported on [0,1].
It is the infimum of the global closed-CDF crossing set, with no supplied
inverse, cut or quantile oracle. Monotonicity and right continuity prove
attainment, and left limits prove the strict-mass bound at atoms. This is a
mathematical construction; computability, a uniform-label coupling, joint
rounding, finite signed order cells and the general minimax comparator are
separate obligations. -/

namespace Blotto.QuantileCDFWitness
open MeasureTheory Set Filter ProbabilityTheory Function
open scoped Topology

def UnitSupported (ρ : ProbabilityMeasure ℝ) : Prop :=
  ∀ᵐ x ∂(ρ : Measure ℝ), x ∈ Icc (0 : ℝ) 1

noncomputable def crossing (ρ : ProbabilityMeasure ℝ) (u : ℝ) : Set ℝ :=
  {x | u ≤ cdf (ρ : Measure ℝ) x}

noncomputable def quantile (ρ : ProbabilityMeasure ℝ) (u : ℝ) : ℝ :=
  sInf (crossing ρ u)

theorem cdf_below_zero (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (x : ℝ) (hx : x < 0) : cdf (ρ : Measure ℝ) x = 0 := by
  have he : Iic x =ᵐ[(ρ : Measure ℝ)] (∅ : Set ℝ) := by
    filter_upwards [hρ] with y hy
    simp only [mem_Iic,mem_empty_iff_false]
    exact propext (iff_false_intro (not_le_of_gt (hx.trans_le hy.1)))
  rw [cdf_eq_real,measureReal_def,measure_congr he,measure_empty,ENNReal.toReal_zero]

theorem cdf_one (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ) :
    cdf (ρ : Measure ℝ) 1 = 1 := by
  have he : Iic (1 : ℝ) =ᵐ[(ρ : Measure ℝ)] (univ : Set ℝ) := by
    filter_upwards [hρ] with y hy
    simp only [mem_Iic,mem_univ]
    exact propext (iff_true_intro hy.2)
  rw [cdf_eq_real,measureReal_def,measure_congr he,measure_univ,ENNReal.toReal_one]

theorem crossing_nonempty (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu : u ≤ 1) : (crossing ρ u).Nonempty := by
  refine ⟨1,?_⟩
  change u ≤ cdf (ρ : Measure ℝ) 1
  rw [cdf_one ρ hρ]
  exact hu

theorem crossing_nonnegative (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu : 0 < u) (x : ℝ) (hx : x ∈ crossing ρ u) : 0 ≤ x := by
  by_contra h
  have hCDF := cdf_below_zero ρ hρ x (lt_of_not_ge h)
  change u ≤ cdf (ρ : Measure ℝ) x at hx
  rw [hCDF] at hx
  exact (not_le_of_gt hu) hx

theorem crossing_bddBelow (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu : 0 < u) : BddBelow (crossing ρ u) :=
  ⟨0,fun x hx => crossing_nonnegative ρ hρ u hu x hx⟩

theorem quantile_nonnegative (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) : 0 ≤ quantile ρ u :=
  le_csInf (crossing_nonempty ρ hρ u hu1) (fun x hx => crossing_nonnegative ρ hρ u hu0 x hx)

theorem quantile_le_one (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) : quantile ρ u ≤ 1 := by
  apply csInf_le (crossing_bddBelow ρ hρ u hu0)
  change u ≤ cdf (ρ : Measure ℝ) 1
  rw [cdf_one ρ hρ]
  exact hu1

theorem quantile_mem_unit (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) : quantile ρ u ∈ Icc (0 : ℝ) 1 :=
  ⟨quantile_nonnegative ρ hρ u hu0 hu1,quantile_le_one ρ hρ u hu0 hu1⟩

theorem quantile_le_of_cdf (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) (x : ℝ) (hx : u ≤ cdf (ρ : Measure ℝ) x) : quantile ρ u ≤ x :=
  csInf_le (crossing_bddBelow ρ hρ u hu0) hx

theorem cdf_lt_of_lt_quantile (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) (x : ℝ) (hx : x < quantile ρ u) : cdf (ρ : Measure ℝ) x < u := by
  by_contra h
  exact (not_le_of_gt hx) (quantile_le_of_cdf ρ hρ u hu0 x (le_of_not_gt h))

theorem level_le_cdf_above_quantile (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (x : ℝ) (hx : quantile ρ u < x) :
    u ≤ cdf (ρ : Measure ℝ) x := by
  obtain ⟨y,hy,hyx⟩ := (csInf_lt_iff (crossing_bddBelow ρ hρ u hu0)
    (crossing_nonempty ρ hρ u hu1)).mp hx
  exact hy.trans ((monotone_cdf (ρ : Measure ℝ)) hyx.le)

theorem level_le_cdf_quantile (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) : u ≤ cdf (ρ : Measure ℝ) (quantile ρ u) := by
  have hRight : Tendsto (cdf (ρ : Measure ℝ)) (𝓝[>] quantile ρ u)
      (𝓝 (cdf (ρ : Measure ℝ) (quantile ρ u))) :=
    ((cdf (ρ : Measure ℝ)).right_continuous (quantile ρ u)).mono Ioi_subset_Ici_self
  apply ge_of_tendsto hRight
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact level_le_cdf_above_quantile ρ hρ u hu0 hu1 x hx

theorem strict_mass_quantile_le (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) : (ρ : Measure ℝ).real (Iio (quantile ρ u)) ≤ u := by
  rw [real_Iio_eq_leftLim]
  apply le_of_tendsto ((monotone_cdf (ρ : Measure ℝ)).tendsto_leftLim (quantile ρ u))
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (cdf_lt_of_lt_quantile ρ hρ u hu0 x hx).le

theorem quantile_cut (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    quantile ρ u ∈ Icc (0 : ℝ) 1 ∧
      (ρ : Measure ℝ).real (Iio (quantile ρ u)) ≤ u ∧
      u ≤ (ρ : Measure ℝ).real (Iic (quantile ρ u)) := by
  refine ⟨quantile_mem_unit ρ hρ u hu0 hu1.le,strict_mass_quantile_le ρ hρ u hu0,?_⟩
  rw [← cdf_eq_real]
  exact level_le_cdf_quantile ρ hρ u hu0 hu1.le

theorem quantile_le_iff_cdf (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (x : ℝ) :
    quantile ρ u ≤ x ↔ u ≤ cdf (ρ : Measure ℝ) x := by
  constructor
  · intro hx
    exact (level_le_cdf_quantile ρ hρ u hu0 hu1).trans ((monotone_cdf (ρ : Measure ℝ)) hx)
  · exact quantile_le_of_cdf ρ hρ u hu0 x

theorem below_quantile_iff_cdf (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (x : ℝ) :
    x < quantile ρ u ↔ cdf (ρ : Measure ℝ) x < u := by
  rw [← not_le,quantile_le_iff_cdf ρ hρ u hu0 hu1 x,not_le]

theorem crossing_eq_Ici (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) : crossing ρ u = Ici (quantile ρ u) := by
  ext x
  exact (quantile_le_iff_cdf ρ hρ u hu0 hu1 x).symm

theorem quantile_mono (ρ : ProbabilityMeasure ℝ) (hρ : UnitSupported ρ)
    (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v) (hv1 : v ≤ 1) (huv : u ≤ v) :
    quantile ρ u ≤ quantile ρ v :=
  quantile_le_of_cdf ρ hρ u hu0 _ (huv.trans (level_le_cdf_quantile ρ hρ v hv0 hv1))

end Blotto.QuantileCDFWitness
