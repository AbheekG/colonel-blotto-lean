import Blotto.FiniteAnchorResponseTransport

/-! Whole-law continuous security is invariant under a finite catalogue
transport preserving field orders and every tuple-budget sign. Real joint
probabilities and duplicate anchors are allowed. Both response directions
are derived from the actual finite-gap construction. -/

namespace Blotto.FiniteAnchorSecurityTransport
open MeasureTheory
open scoped BigOperators Classical
open FiniteAnchorResponseTransport

noncomputable def rowMap {m K : ℕ} (old target : Fin m → Fin K → ℝ)
    (row : Allocation m) : Allocation m :=
  fun field => FiniteAnchorTransport.relabel (old field) (target field) (row field)

theorem rowMap_measurable {m K : ℕ} (old target : Fin m → Fin K → ℝ) :
    Measurable (rowMap old target) := by
  apply Measurable.of_eval
  intro field
  exact (FiniteAnchorTransport.relabel_measurable _ _).comp (measurable_pi_apply field)

theorem rowMap_labelled {m K : ℕ} (old target : Fin m → Fin K → ℝ) (budget : ℝ)
    (h : Catalogue old target budget) (labels : Fin m → Fin K) :
    rowMap old target (fun field => old field (labels field)) =
      fun field => target field (labels field) := by
  funext field
  exact FiniteAnchorTransport.relabel_at_anchor _ _
    (fun i j hij => (h.equal field i j).mp hij) _

theorem purePayoff_map_exact {m K : ℕ} (values : Values m) (old target : Fin m → Fin K → ℝ)
    (budget : ℝ) (h : Catalogue old target budget) (law : Mixed m)
    (hFinite : ∀ᵐ row ∂(law : Measure (Allocation m)),
      ∃ labels : Fin m → Fin K, row = fun field => old field (labels field))
    (y z : Allocation m)
    (hShares : ∀ field label, share (y field) (old field label) = share (z field) (target field label)) :
    purePayoff values y law = purePayoff values z (law.map (rowMap old target)) := by
  unfold purePayoff
  change _ = ∫ row, payoff values z row ∂Measure.map (rowMap old target) (law : Measure (Allocation m))
  rw [integral_map (rowMap_measurable old target).aemeasurable
    (integrable_payoff_right values z (law.map (rowMap old target))).aestronglyMeasurable]
  apply integral_congr_ae
  exact hFinite.mono fun row hr => by
    obtain ⟨labels,rfl⟩ := hr
    dsimp only
    rw [rowMap_labelled old target budget h labels]
    unfold payoff
    exact Finset.sum_congr rfl (fun field _ => congrArg (fun t => values.weight field * t) (hShares field _))

/-- Equality of the actual sets of all feasible-response payoffs, hence of
the continuous supremum. No finite response ceiling or response oracle is
supplied, and no maximum or uniform label weights are claimed. -/
theorem security_map_eq {m K : ℕ} (values : Values m) (old target : Fin m → Fin K → ℝ)
    (budget : ℝ) (h : Catalogue old target budget)
    (hOld : ∀ field label, 0 ≤ old field label) (law : Mixed m)
    (hFinite : ∀ᵐ row ∂(law : Measure (Allocation m)),
      ∃ labels : Fin m → Fin K, row = fun field => old field (labels field)) :
    security values budget (law.map (rowMap old target)) = security values budget law := by
  unfold security
  congr 1
  ext value
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨y,hy,hShares⟩ := response_exists target old budget (h.reverse hOld) z hz
    refine ⟨y,hy,?_⟩
    exact purePayoff_map_exact values old target budget h law hFinite y z
      (fun field label => (hShares field label).symm)
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨z,hz,hShares⟩ := response_exists old target budget h y hy
    refine ⟨z,hz,?_⟩
    exact (purePayoff_map_exact values old target budget h law hFinite y z hShares).symm

end Blotto.FiniteAnchorSecurityTransport
