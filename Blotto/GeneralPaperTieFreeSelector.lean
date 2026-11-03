import Blotto.GeneralPaperAtomlessRegularTransfer
import Mathlib.MeasureTheory.Measure.Prod

/-! An atomless-marginal whole law almost surely avoids every coordinate
tie against an arbitrary opposing whole law. An above-average pure row can
be chosen from that tie-free set. -/
namespace Blotto.GeneralPaperTieFreeSelector
open MeasureTheory RichSmoothingLaw
set_option autoImplicit false
set_option maxHeartbeats 2500000

def TieFree {n : ℕ} (x : Allocation n) (opponent : Mixed n) : Prop :=
  ∀ᵐ y ∂(opponent : Measure (Allocation n)), ∀ j, x j ≠ y j

theorem smooth_ae_avoids_bid {n : ℕ} (smooth : Mixed n)
    (hAtomless : GeneralPaperAtomlessRegularTransfer.AtomlessMarginals smooth)
    (j : Fin n) (z : ℝ) :
    ∀ᵐ x ∂(smooth : Measure (Allocation n)), x j ≠ z := by
  let : NullSingletonClass (marginal smooth j : Measure ℝ) := ⟨hAtomless j⟩
  have h := Measure.ae_ne (marginal smooth j : Measure ℝ) z
  change ∀ᵐ v ∂(Measure.map (fun x : Allocation n => x j)
      (smooth : Measure (Allocation n))), v ≠ z at h
  exact (ae_map_iff (measurable_pi_apply j).aemeasurable
    (isClosed_singleton.isOpen_compl.measurableSet)).mp h

theorem tie_free_ae {n : ℕ} (smooth opponent : Mixed n)
    (hAtomless : GeneralPaperAtomlessRegularTransfer.AtomlessMarginals smooth) :
    ∀ᵐ x ∂(smooth : Measure (Allocation n)), TieFree x opponent := by
  have hmeas' : MeasurableSet
      (⋂ j, {z : Allocation n × Allocation n | z.1 j ≠ z.2 j}) := by
    apply MeasurableSet.iInter
    intro j
    have hfirst : Continuous (fun z : Allocation n × Allocation n => z.1 j) :=
      (continuous_apply j).comp continuous_fst
    have hsecond : Continuous (fun z : Allocation n × Allocation n => z.2 j) :=
      (continuous_apply j).comp continuous_snd
    have heq : MeasurableSet
        {z : Allocation n × Allocation n | z.1 j = z.2 j} :=
      (isClosed_eq hfirst hsecond).measurableSet
    simpa only [Set.compl_ofPred] using heq.compl
  have hmeas : MeasurableSet
      {z : Allocation n × Allocation n | ∀ j, z.1 j ≠ z.2 j} := by
    simpa only [Set.ofPred_forall] using hmeas'
  have hright : ∀ᵐ y ∂(opponent : Measure (Allocation n)),
      ∀ᵐ x ∂(smooth : Measure (Allocation n)), ∀ j, x j ≠ y j := by
    apply Filter.Eventually.of_forall
    intro y
    apply ae_all_iff.mpr
    intro j
    exact smooth_ae_avoids_bid smooth hAtomless j (y j)
  exact (Measure.ae_ae_comm hmeas).mpr hright

theorem exists_tie_free_above_average {n : ℕ} (values : Values n)
    {budget : ℝ} (smooth opponent : Mixed n)
    (hRegular : Regular budget smooth) (epsilon : ℝ) (he : 0<epsilon) :
    ∃ x : Allocation n, FullBudget budget x ∧ TieFree x opponent ∧
      expected values smooth opponent-epsilon < purePayoff values x opponent := by
  have hgood : ∀ᵐ x ∂(smooth : Measure (Allocation n)),
      FullBudget budget x ∧ TieFree x opponent := by
    filter_upwards [hRegular.1,
      tie_free_ae smooth opponent (GeneralPaperAtomlessRegularTransfer.rich_regular_atomless hRegular)]
      with x hx ht
    exact ⟨hx.1,ht⟩
  by_contra hnone
  have hpoint : ∀ᵐ x ∂(smooth : Measure (Allocation n)),
      purePayoff values x opponent≤expected values smooth opponent-epsilon := by
    filter_upwards [hgood] with x hx
    exact le_of_not_gt (fun hgt => hnone ⟨x,hx.1,hx.2,hgt⟩)
  have hIntegral := integral_mono_ae
    (integrable_purePayoff values smooth opponent)
    (integrable_const (expected values smooth opponent-epsilon)) hpoint
  rw [←expected_iterated] at hIntegral
  simp at hIntegral
  linarith

theorem exists_tie_free_near_pure {n : ℕ} (values : Values n)
    (x : Allocation n) {A B : ℝ} (hA : 0<A) (hX : FullBudget A x)
    (hn : 2≤n) (hBudgets : B<A)
    (opponent : Mixed n) (hOpponent : Supported B opponent)
    (epsilon : ℝ) (he : 0<epsilon) :
    ∃ x' : Allocation n, FullBudget A x' ∧ TieFree x' opponent ∧
      purePayoff values x opponent-epsilon < purePayoff values x' opponent := by
  have hhalf : 0<epsilon/2 := by linarith
  obtain ⟨smooth,hRegular,happrox⟩ :=
    RichSmoothingApproximation.exists_regular_approximation
      values x hA hX hn hBudgets opponent hOpponent (epsilon/2) hhalf
  obtain ⟨x',hFull,hTie,hgood⟩ :=
    exists_tie_free_above_average values smooth opponent hRegular (epsilon/2) hhalf
  refine ⟨x',hFull,hTie,?_⟩
  linarith

end Blotto.GeneralPaperTieFreeSelector
