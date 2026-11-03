import Blotto.GeneralPaperCatalogueContinuousSecurity

/-! Real-weight whole-law realization of a probability measure supported
on finitely many distinct rows. This proof comparator conversion preserves
the exact joint law and does not enumerate or rationalize its probabilities
as part of the runtime source.
-/
namespace Blotto.GeneralPaperFiniteAtomicLaw
open MeasureTheory Set
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem sum_atoms {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {N : ℕ}
    (law : ProbabilityMeasure α) (point : Fin N → α) (hInjective : Function.Injective point)
    (hSupport : ∀ᵐ x ∂(law:Measure α), x∈Set.range point) :
    Measure.sum (fun i => (law:Measure α) {point i} • Measure.dirac (point i))=(law:Measure α) := by
  ext s hs
  have hd : Pairwise (fun i j : Fin N => Disjoint ({point i}∩s) ({point j}∩s)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hx hj
    have he : point i=point j := hx.1.symm.trans hj.1
    exact hij (hInjective he)
  have heq : s =ᵐ[(law:Measure α)] ⋃ i : Fin N, ({point i}∩s) := by
    filter_upwards [hSupport] with x hx
    obtain ⟨i,rfl⟩ := hx
    apply propext
    constructor
    · intro hi
      exact Set.mem_iUnion.mpr ⟨i,⟨rfl,hi⟩⟩
    · intro hi
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hi
      exact hj.2
  calc
    _ = ∑' i : Fin N, (law:Measure α) {point i}*(Measure.dirac (point i)) s := by
      rw [Measure.sum_apply _ hs]
      simp only [Measure.smul_apply,smul_eq_mul]
    _ = ∑' i : Fin N, (law:Measure α) ({point i}∩s) := by
      apply tsum_congr
      intro i
      by_cases hi : point i∈s
      · simp [Measure.dirac_apply',hs,hi]
      · simp [Measure.dirac_apply',hs,hi]
    _ = (law:Measure α) (⋃ i : Fin N, ({point i}∩s)) := (measure_iUnion hd (fun i => (measurableSet_singleton (point i)).inter hs)).symm
    _ = (law:Measure α) s := (measure_congr heq).symm

noncomputable def weight {α : Type*} [MeasurableSpace α] {N : ℕ} (law : ProbabilityMeasure α) (point : Fin N → α) (i : Fin N) : ℝ :=
  (law:Measure α).real {point i}

theorem weight_nonnegative {α : Type*} [MeasurableSpace α] {N : ℕ} (law : ProbabilityMeasure α) (point : Fin N → α) (i : Fin N) :
    0≤weight law point i := ENNReal.toReal_nonneg

theorem weight_total {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {N : ℕ}
    (law : ProbabilityMeasure α) (point : Fin N → α) (hInjective : Function.Injective point)
    (hSupport : ∀ᵐ x ∂(law:Measure α), x∈Set.range point) : ∑ i, weight law point i=1 := by
  have hm := congrArg (fun μ : Measure α => μ Set.univ) (sum_atoms law point hInjective hSupport)
  simp only [Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply_of_mem (Set.mem_univ _),mul_one,measure_univ,tsum_fintype] at hm
  have hr := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top (law:Measure α) {point i})] at hr
  simpa only [weight,Measure.real,ENNReal.toReal_one] using hr

theorem realization {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {N : ℕ}
    (law : ProbabilityMeasure α) (point : Fin N → α) (hInjective : Function.Injective point)
    (hSupport : ∀ᵐ x ∂(law:Measure α), x∈Set.range point) :
    probabilityMixture (weight law point) (fun i => (⟨Measure.dirac (point i),inferInstance⟩:ProbabilityMeasure α))
      (weight_nonnegative law point) (weight_total law point hInjective hSupport)=law := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.sum (fun i => ENNReal.ofReal (weight law point i) • Measure.dirac (point i))=(law:Measure α)
  have hw (i : Fin N) : ENNReal.ofReal (weight law point i)=(law:Measure α) {point i} :=
    ofReal_measureReal (by finiteness)
  simp only [hw]
  exact sum_atoms law point hInjective hSupport

end Blotto.GeneralPaperFiniteAtomicLaw
