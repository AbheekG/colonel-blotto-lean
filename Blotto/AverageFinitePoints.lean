import Blotto.ParameterLaw
import Blotto.FiniteUniformPoints

/-! Averaging a measurable family over a finite scalar law is exactly its
finite weighted whole-law mixture. The parameter may first be transported
through a measurable map, so nonlinear location draws are included. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

theorem averaged_finiteUniform_map {N n : ℕ} (hN : 0 < N) (point : Fin N → ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (law : ℝ → Mixed n) (hlaw : Measurable (fun s => (law s : Measure (Allocation n)))) :
    averagedLaw ((finiteUniformPoints hN point).map f) law hlaw =
      probabilityMixture (fun _ : Fin N => 1 / (N : ℝ)) (fun j => law (f (point j)))
        (fun _ => by positivity) (uniformWeights_sum hN) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.map f (mixtureMeasure (fun _ : Fin N => 1 / (N : ℝ)) (fun j => realPointLaw (point j)))).bind
    (fun s => (law s : Measure (Allocation n))) = _
  rw [mixtureMeasure_map _ _ _ hf, Measure.bind_sum _ _ hlaw.aemeasurable]
  change Measure.sum (fun j : Fin N =>
      (ENNReal.ofReal (1 / (N : ℝ)) • Measure.map f (Measure.dirac (point j))).bind (fun s => (law s : Measure (Allocation n)))) =
    Measure.sum (fun j : Fin N => ENNReal.ofReal (1 / (N : ℝ)) • (law (f (point j)) : Measure (Allocation n)))
  congr 1
  funext j
  rw [Measure.bind_smul _ _ hlaw.aemeasurable, Measure.map_dirac' hf, Measure.dirac_bind hlaw]

end Blotto
