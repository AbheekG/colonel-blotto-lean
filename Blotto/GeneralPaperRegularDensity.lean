import Blotto.GeneralPaperTieFreeSelector
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba

/-! Convolution along full-budget affine segments gives atomless-marginal
whole laws converging to any full-budget strategy in the weak topology. -/
namespace Blotto.GeneralPaperRegularDensity
open MeasureTheory Filter RichSmoothingLaw
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 2500000

def affine {n : ℕ} (eta : ℝ) (pair : Allocation n × Allocation n) : Allocation n :=
  fun j => (1-eta)*pair.1 j+eta*pair.2 j

theorem continuous_affine {n : ℕ} :
    Continuous (fun p : ℝ × (Allocation n × Allocation n) => affine p.1 p.2) := by
  apply continuous_pi
  intro j
  change Continuous (fun p : ℝ × (Allocation n × Allocation n) =>
    (1-p.1)*p.2.1 j+p.1*p.2.2 j)
  fun_prop

theorem continuous_affine_fixed {n : ℕ} (eta : ℝ) :
    Continuous (affine (n := n) eta) := by
  apply continuous_pi
  intro j
  change Continuous (fun pair : Allocation n × Allocation n =>
    (1-eta)*pair.1 j+eta*pair.2 j)
  fun_prop

theorem affine_zero {n : ℕ} (pair : Allocation n × Allocation n) :
    affine 0 pair=pair.1 := by
  funext j
  simp [affine]

noncomputable def perturb {n : ℕ} (mu z : Mixed n) (eta : ℝ) : Mixed n :=
  (mu.prod z).map (affine eta)

private theorem param_eq_perturb {n : ℕ} (mu z : Mixed n) (eta : ℝ) :
    ((diracProba eta).prod (mu.prod z)).map
      (fun p : ℝ × (Allocation n × Allocation n) => affine p.1 p.2)=
    perturb mu z eta := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun p : ℝ × (Allocation n × Allocation n) => affine p.1 p.2)
      ((Measure.dirac eta).prod ((mu.prod z : ProbabilityMeasure (Allocation n × Allocation n)) :
        Measure (Allocation n × Allocation n))) =
    Measure.map (affine eta)
      ((mu.prod z : ProbabilityMeasure (Allocation n × Allocation n)) :
        Measure (Allocation n × Allocation n))
  rw [Measure.dirac_prod,Measure.map_map]
  · rfl
  · exact continuous_affine.measurable
  · exact measurable_prodMk_left

theorem perturb_zero {n : ℕ} (mu z : Mixed n) : perturb mu z 0=mu := by
  change (mu.prod z).map (affine 0)=mu
  have h : affine 0=fun pair : Allocation n × Allocation n => pair.1 := by
    funext pair
    exact affine_zero pair
  rw [h]
  exact ProbabilityMeasure.map_fst_prod (μ := mu) (ν := z)

theorem perturb_continuous {n : ℕ} (mu z : Mixed n) :
    Continuous (perturb mu z) := by
  have hprod : Continuous (fun eta : ℝ => (diracProba eta).prod (mu.prod z)) :=
    ProbabilityMeasure.continuous_prod.comp
      (continuous_diracProba.prodMk continuous_const)
  have hmap : Continuous (fun eta : ℝ =>
      ((diracProba eta).prod (mu.prod z)).map
        (fun p : ℝ × (Allocation n × Allocation n) => affine p.1 p.2)) :=
    (ProbabilityMeasure.continuous_map continuous_affine).comp hprod
  simpa only [param_eq_perturb] using hmap

theorem perturb_tendsto_zero {n : ℕ} (mu z : Mixed n) :
    Tendsto (perturb mu z) (𝓝 (0:ℝ)) (𝓝 mu) := by
  have h : Tendsto (perturb mu z) (𝓝 (0:ℝ)) (𝓝 (perturb mu z 0)) :=
    (perturb_continuous mu z).continuousAt.tendsto
  rwa [perturb_zero] at h

theorem perturb_atomless {n : ℕ} (mu z : Mixed n)
    (hz : GeneralPaperAtomlessRegularTransfer.AtomlessMarginals z)
    (eta : ℝ) (hEta : 0<eta) :
    GeneralPaperAtomlessRegularTransfer.AtomlessMarginals (perturb mu z eta) := by
  intro j t
  let S : Set (Allocation n × Allocation n) :=
    {pair | affine eta pair j=t}
  have hS : MeasurableSet S := by
    exact (measurable_pi_apply j |>.comp (continuous_affine_fixed eta).measurable)
      (measurableSet_singleton t)
  have hsection (x : Allocation n) :
      (z : Measure (Allocation n)) ((Prod.mk x) ⁻¹' S)=0 := by
    let target := (t-(1-eta)*x j)/eta
    have hset : (Prod.mk x) ⁻¹' S = {y : Allocation n | y j=target} := by
      ext y
      change (1-eta)*x j+eta*y j=t ↔ y j=target
      constructor
      · intro h
        apply (eq_div_iff (ne_of_gt hEta)).mpr
        nlinarith
      · intro h
        have hh := (eq_div_iff (ne_of_gt hEta)).mp h
        nlinarith
    rw [hset]
    have hae := GeneralPaperTieFreeSelector.smooth_ae_avoids_bid z hz j target
    simpa only [ae_iff, Classical.not_not] using hae
  change Measure.map (fun row : Allocation n => row j)
    (Measure.map (affine eta)
      ((mu.prod z : ProbabilityMeasure (Allocation n × Allocation n)) :
        Measure (Allocation n × Allocation n))) {t}=0
  rw [Measure.map_map (measurable_pi_apply j) (continuous_affine_fixed eta).measurable]
  rw [Measure.map_apply
    ((measurable_pi_apply j).comp (continuous_affine_fixed eta).measurable)
    (measurableSet_singleton t)]
  change ((mu : Measure (Allocation n)).prod (z : Measure (Allocation n))) S=0
  rw [Measure.prod_apply hS]
  simp only [hsection,lintegral_zero]

theorem affine_fullBudget {n : ℕ} (B eta : ℝ)
    (hEta : 0≤eta ∧ eta≤1) (x z : Allocation n)
    (hx : FullBudget B x) (hz : FullBudget B z) :
    FullBudget B (affine eta (x,z)) := by
  constructor
  · intro j
    change 0≤(1-eta)*x j+eta*z j
    have h1 := mul_nonneg (by linarith : 0≤1-eta) (hx.1 j)
    have h2 := mul_nonneg hEta.1 (hz.1 j)
    linarith
  · simp only [affine,Finset.sum_add_distrib,← Finset.mul_sum,hx.2,hz.2]
    ring

theorem perturb_fullBudget {n : ℕ} {B : ℝ} (mu z : Mixed n)
    (hmu : ∀ᵐ x ∂(mu : Measure (Allocation n)), FullBudget B x)
    (hz : Regular B z) (eta : ℝ) (hEta : 0≤eta ∧ eta≤1) :
    ∀ᵐ row ∂(perturb mu z eta : Measure (Allocation n)), FullBudget B row := by
  have hset : MeasurableSet
      {pair : Allocation n × Allocation n | FullBudget B (affine eta pair)} :=
    (continuous_affine_fixed eta).measurable (measurable_fullBudget B)
  have hpair : ∀ᵐ pair ∂((mu : Measure (Allocation n)).prod
      (z : Measure (Allocation n))), FullBudget B (affine eta pair) :=
    (Measure.ae_prod_iff_ae_ae hset).mpr
      (hmu.mono fun x hx => (hz.1).mono fun z hz' =>
        affine_fullBudget B eta hEta x z hx hz'.1)
  change ∀ᵐ row ∂Measure.map (affine eta)
    ((mu : Measure (Allocation n)).prod (z : Measure (Allocation n))),
      FullBudget B row
  exact (ae_map_iff (continuous_affine_fixed eta).measurable.aemeasurable
    (measurable_fullBudget B)).mpr hpair

theorem weak_dense_atomless {n : ℕ} {B : ℝ} (mu z : Mixed n)
    (hmu : ∀ᵐ x ∂(mu : Measure (Allocation n)), FullBudget B x)
    (hz : Regular B z) (U : Set (Mixed n)) (hU : U∈𝓝 mu) :
    ∃ eta : ℝ, 0<eta ∧ eta<1 ∧ perturb mu z eta∈U ∧
      (∀ᵐ row ∂(perturb mu z eta : Measure (Allocation n)), FullBudget B row) ∧
      GeneralPaperAtomlessRegularTransfer.AtomlessMarginals (perturb mu z eta) := by
  let t : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have ht : Tendsto t atTop (𝓝 (0:ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hnear := ((perturb_tendsto_zero mu z).comp ht).eventually hU
  have hvalid : ∀ᶠ k : ℕ in atTop, 0<t k ∧ t k<1 := by
    apply Filter.eventually_atTop.2
    refine ⟨1,?_⟩
    intro k hk
    have hd : (1:ℝ)<(k:ℝ)+1 := by exact_mod_cast (by omega : 1<k+1)
    dsimp only [t]
    constructor
    · positivity
    · apply (div_lt_iff₀ (by linarith : 0<(k:ℝ)+1)).mpr
      linarith
  obtain ⟨k,hU',hk⟩ := (hnear.and hvalid).exists
  exact ⟨t k,hk.1,hk.2,hU',
    perturb_fullBudget mu z hmu hz (t k) ⟨hk.1.le,hk.2.le⟩,
    perturb_atomless mu z hz.2 (t k) hk.1⟩

theorem atomless_fullBudget_dense {n : ℕ} {B : ℝ} (mu : Mixed n)
    (hB : 0 < B) (hn : 2 ≤ n)
    (hmu : ∀ᵐ x ∂(mu : Measure (Allocation n)), FullBudget B x)
    (U : Set (Mixed n)) (hU : U ∈ 𝓝 mu) :
    ∃ nu : Mixed n, nu ∈ U ∧
      (∀ᵐ row ∂(nu : Measure (Allocation n)), FullBudget B row) ∧
      GeneralPaperAtomlessRegularTransfer.AtomlessMarginals nu := by
  obtain ⟨x,hx⟩ := hmu.exists
  let h := RichSmoothingGeometry.active_nonempty x B hB hx
  let t := RichSmoothingGeometry.radius x h / 2
  have ht : 0 < t := by
    dsimp [t]
    have hr := RichSmoothingGeometry.radius_positive x h
    linarith
  have htr : t ≤ RichSmoothingGeometry.radius x h := by
    dsimp [t]
    linarith [RichSmoothingGeometry.radius_positive x h]
  let z := RichSmoothingLaw.law x h t
  have hz : Regular B z := RichSmoothingLaw.law_regular x B hB hx hn t ht htr
  obtain ⟨eta,_,_,hU',hfull,hatom⟩ := weak_dense_atomless mu z hmu hz U hU
  exact ⟨perturb mu z eta,hU',hfull,hatom⟩

end Blotto.GeneralPaperRegularDensity
