import Blotto.RealFamilyFirst
import Blotto.RealResidualSampler
import Blotto.RealBinaryFlat
import Blotto.NestedThird

/-! Exact continuous middle nested case, including v=0, using one fresh
branch uniform and the first-family or explicit residual continuation. -/

namespace Blotto.NestedInput
open MeasureTheory
open scoped Classical

noncomputable def realThirdSample (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u)
    (seed : Fin 11 → ℝ) : Allocation 3 :=
  if hv : 0 < i.v then
    realBinarySample (RationalNestedParametersCode.thirdAlpha.realValue (RealNestedParametersCode.environment i 0)) (i.realFamilyFirstSample i.v hv le_rfl)
      (i.residualInput hvt htu).realSample seed
  else (i.residualInput hvt htu).realSample (Fin.tail seed)

theorem realThirdSample_refines (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) :
    i.realThirdSample hvt htu = fun seed =>
      if hv : 0 < i.v then realBinarySample i.thirdAlpha
        (i.realFamilyFirstSample i.v hv le_rfl) (i.residualInput hvt htu).realSample seed
      else (i.residualInput hvt htu).realSample (Fin.tail seed) := by
  funext seed
  simp only [realThirdSample, RealNestedParametersCode.thirdAlpha_value]

theorem realThirdSample_measurable (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) :
    Measurable (i.realThirdSample hvt htu) := by
  rw [i.realThirdSample_refines hvt htu]
  change Measurable (fun seed => if hv : 0 < i.v then _ else _)
  by_cases hv : 0 < i.v
  · simp only [dite_eq_left hv]
    exact realBinarySample_measurable i.thirdAlpha _ _ (i.realFamilyFirstSample_measurable _ _ _)
      (i.residualInput hvt htu).realSample_measurable
  · simp only [dite_eq_right hv]
    exact (i.residualInput hvt htu).realSample_measurable.comp (RealUniformInputs.measurable_tail 10)

theorem realThirdSample_law (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) :
    Measure.map (i.realThirdSample hvt htu) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) =
      (i.thirdLaw hvt htu : Measure (Allocation 3)) := by
  rw [i.realThirdSample_refines hvt htu]
  change Measure.map (fun seed => if hv : 0 < i.v then _ else _) _ = _
  by_cases hv : 0 < i.v
  · simp only [thirdLaw, dite_eq_left hv]
    exact realBinarySample_realizes i.thirdAlpha _ _ _ (i.realFamilyFirstSample_measurable _ _ _)
      (i.residualInput hvt htu).realSample_measurable _ _
      (i.realFamilyFirstSample_law _ _ _) (i.residualInput hvt htu).realSample_law
  · simp only [thirdLaw, dite_eq_right hv]
    change Measure.map ((i.residualInput hvt htu).realSample ∘
      (Fin.tail : (Fin 11 → ℝ) → (Fin 10 → ℝ))) _ = _
    rw [← Measure.map_map (i.residualInput hvt htu).realSample_measurable (RealUniformInputs.measurable_tail 10),
      RealUniformInputs.tail_law 10]
    exact (i.residualInput hvt htu).realSample_law

theorem realThirdSample_fullBudget (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u)
    (seed : Fin 11 → ℝ) (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) :
    FullBudget i.M (i.realThirdSample hvt htu seed) := by
  have hResidual : FullBudget i.M ((i.residualInput hvt htu).realSample (Fin.tail seed)) := by
    have hB : (i.residualInput hvt htu).g.budget = i.M := i.geometry_matches.2.2.2
    simpa only [hB] using (i.residualInput hvt htu).realSample_fullBudget (Fin.tail seed) (fun j => h j.succ)
  unfold realThirdSample
  split_ifs with hv
  · exact realBinarySample_predicate _ _ _ seed (FullBudget i.M)
      (i.realFamilyFirstSample_fullBudget _ _ _ (Fin.tail seed) (h 1) (h 2)) hResidual
  · exact hResidual

end Blotto.NestedInput
