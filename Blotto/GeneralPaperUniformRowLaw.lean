import Blotto.GeneralPaperCircleQuantileComparison
import Blotto.FiniteMixturePayoff

/-! Actual uniform laws on whole real allocation rows. Nested draws retain
all within-row dependence. These are erased probability-law semantics;
native fair-bit sampling and its prices remain separate obligations. -/
namespace Blotto.GeneralPaperUniformRowLaw
open MeasureTheory
open GeneralPaperCircleFiniteAverage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable def point {n : ℕ} (x : Allocation n) : Mixed n :=
  ⟨Measure.dirac x,inferInstance⟩

noncomputable def mixture {n N : ℕ} (hN : 0<N) (laws : Fin N → Mixed n) : Mixed n :=
  probabilityMixture (fun _ => 1/(N:ℝ)) laws (fun _ => by positivity) (uniformWeights_sum hN)

noncomputable def law {n N : ℕ} (hN : 0<N) (rows : Fin N → Allocation n) : Mixed n :=
  mixture hN (fun i => point (rows i))

theorem mixture_supported {n N : ℕ} (hN : 0<N) (laws : Fin N → Mixed n) (B : ℝ)
    (h : ∀ i,Supported B (laws i)) : Supported B (mixture hN laws) :=
  probabilityMixture_supported B _ _ _ _ h

theorem law_supported {n N : ℕ} (hN : 0<N) (rows : Fin N → Allocation n) (B : ℝ)
    (h : ∀ i,Feasible B (rows i)) : Supported B (law hN rows) := by
  apply mixture_supported
  intro i
  change ∀ᵐ x ∂Measure.dirac (rows i),Feasible B x
  rw [ae_dirac_eq]
  exact h i

theorem pure_mixture {n N : ℕ} (hN : 0<N) (laws : Fin N → Mixed n) (v : Values n) (y : Allocation n) :
    purePayoff v y (mixture hN laws)=GeneralPaperCircleFiniteAverage.average (fun i => purePayoff v y (laws i)) := by
  unfold purePayoff mixture
  rw [probabilityMixture_integral _ _ _ _ _ (fun i => integrable_payoff_right v y (laws i))]
  unfold GeneralPaperCircleFiniteAverage.average
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pure_law {n N : ℕ} (hN : 0<N) (rows : Fin N → Allocation n) (v : Values n) (y : Allocation n) :
    purePayoff v y (law hN rows)=GeneralPaperCircleFiniteAverage.average (fun i => payoff v y (rows i)) := by
  rw [law,pure_mixture]
  congr 1
  funext i
  change (∫ x,payoff v y x ∂Measure.dirac (rows i))=payoff v y (rows i)
  exact integral_dirac _ _

end Blotto.GeneralPaperUniformRowLaw
