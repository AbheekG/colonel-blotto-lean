import Blotto.GeneralPaperLightFieldIndexEquiv

/-! Exact change of named battlefield indices for arbitrary whole-allocation
laws. Hard at-most feasibility, ties and canonical continuous security are
preserved, even when the two index types have different dimension expressions. -/
namespace Blotto.GeneralPaperFieldRelabel
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

def allocation {m n : ℕ} (e : Fin m ≃ Fin n) (x : Allocation n) : Allocation m := fun j => x (e j)

theorem measurable_allocation {m n : ℕ} (e : Fin m ≃ Fin n) : Measurable (allocation e) := by
  apply Measurable.of_eval
  intro j
  exact measurable_pi_apply (e j)

theorem inverse {m n : ℕ} (e : Fin m ≃ Fin n) (x : Allocation m) :
    allocation e (allocation e.symm x)=x := by
  funext j
  simp only [allocation,Equiv.symm_apply_apply]

theorem feasible_iff {m n : ℕ} (e : Fin m ≃ Fin n) (B : ℝ) (x : Allocation n) :
    Feasible B (allocation e x) ↔ Feasible B x := by
  constructor
  · intro h
    constructor
    · intro j
      simpa only [allocation,Equiv.apply_symm_apply] using h.1 (e.symm j)
    · simpa only [allocation,Equiv.sum_comp] using h.2
  · intro h
    exact ⟨fun j => h.1 (e j),by simpa only [allocation,Equiv.sum_comp] using h.2⟩

noncomputable def values {m n : ℕ} (e : Fin m ≃ Fin n) (v : Values n) : Values m where
  weight := fun j => v.weight (e j)
  positive := fun j => v.positive (e j)
  normalized := (Equiv.sum_comp e v.weight).trans v.normalized

theorem values_inverse {m n : ℕ} (e : Fin m ≃ Fin n) (v : Values n) :
    values e.symm (values e v)=v := by
  cases v
  unfold values
  congr 1
  funext j
  exact congrArg _ (e.apply_symm_apply j)

theorem payoff_relabel {m n : ℕ} (e : Fin m ≃ Fin n) (v : Values n) (x y : Allocation n) :
    payoff (values e v) (allocation e x) (allocation e y)=payoff v x y := by
  unfold payoff values allocation
  exact Equiv.sum_comp e (fun j => v.weight j*share (x j) (y j))

noncomputable def law {m n : ℕ} (e : Fin m ≃ Fin n) (μ : Mixed n) : Mixed m := μ.map (allocation e)

theorem law_inverse {m n : ℕ} (e : Fin m ≃ Fin n) (μ : Mixed m) : law e (law e.symm μ)=μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (allocation e) (Measure.map (allocation e.symm) (μ:Measure (Allocation m)))=(μ:Measure (Allocation m))
  rw [Measure.map_map (measurable_allocation e) (measurable_allocation e.symm)]
  have he : (allocation e) ∘ (allocation e.symm)=id := by
    funext x
    exact inverse e x
  rw [he,Measure.map_id]

theorem supported {m n : ℕ} (e : Fin m ≃ Fin n) (μ : Mixed n) (B : ℝ) (h : Supported B μ) :
    Supported B (law e μ) := by
  change ∀ᵐ x ∂Measure.map (allocation e) (μ:Measure (Allocation n)),Feasible B x
  rw [ae_map_iff (measurable_allocation e).aemeasurable (measurable_feasible B)]
  exact h.mono (fun x hx => (feasible_iff e B x).mpr hx)

theorem pure_relabel {m n : ℕ} (e : Fin m ≃ Fin n) (v : Values n) (x : Allocation n) (μ : Mixed n) :
    purePayoff (values e v) (allocation e x) (law e μ)=purePayoff v x μ := by
  unfold purePayoff
  change (∫ y,payoff (values e v) (allocation e x) y ∂Measure.map (allocation e) (μ:Measure (Allocation n)))=_
  rw [integral_map (measurable_allocation e).aemeasurable
    (integrable_payoff_right (values e v) (allocation e x) (law e μ)).aestronglyMeasurable]
  simp_rw [payoff_relabel]

theorem security_relabel {m n : ℕ} (e : Fin m ≃ Fin n) (v : Values n) (B : ℝ) (μ : Mixed n) :
    security (values e v) B (law e μ)=security v B μ := by
  unfold security
  congr 1
  ext z
  constructor
  · rintro ⟨x,hx,hz⟩
    let y := allocation e.symm x
    have he : allocation e y=x := inverse e x
    have hy : Feasible B y := (feasible_iff e B y).mp (by rw [he];exact hx)
    refine ⟨y,hy,?_⟩
    change purePayoff v y μ=z
    rw [←pure_relabel e v y μ,he]
    exact hz
  · rintro ⟨x,hx,hz⟩
    refine ⟨allocation e x,(feasible_iff e B x).mpr hx,?_⟩
    change purePayoff (values e v) (allocation e x) (law e μ)=z
    rw [pure_relabel]
    exact hz

theorem restored_security {m n : ℕ} (e : Fin m ≃ Fin n) (v : Values n) (B : ℝ) (μ : Mixed m) :
    security v B (law e.symm μ)=security (values e v) B μ := by
  have h := security_relabel e v B (law e.symm μ)
  rw [law_inverse] at h
  exact h.symm

end Blotto.GeneralPaperFieldRelabel
