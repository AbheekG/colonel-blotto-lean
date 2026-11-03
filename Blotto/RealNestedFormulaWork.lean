import Blotto.RealNestedSpecSampler

/-! Selected-path allowances for the counted formula stages of nested sampling.
These include the actual scalar expression evaluations and complete geometry
or residual descriptors. Primitive control, native parameter constructors,
categorical/interpolation work and physical storage costs are separate. -/

namespace Blotto
open scoped Classical

namespace RealNestedParametersCode
open RationalNestedParametersCode

theorem location_operations (i : NestedInput) (x : ℝ) :
    (RationalNestedParametersCode.location.runReal (environment i x)).2 ≤ 128 := by
  simpa [scalarPrograms] using scalar_operations i x 0

theorem conditional_operations (i : NestedInput) (x : ℝ) :
    (RationalNestedParametersCode.conditional.runReal (environment i x)).2 ≤ 128 := by
  simpa [scalarPrograms] using scalar_operations i x 1

theorem familyProbability_operations (i : NestedInput) (x : ℝ) :
    (RationalNestedParametersCode.familyProbability.runReal (environment i x)).2 ≤ 128 := by
  simpa [scalarPrograms] using scalar_operations i x 2

theorem mirror_operations (i : NestedInput) :
    (RationalNestedParametersCode.mirror.runReal (environment i 0)).2 ≤ 128 := by
  simpa [scalarPrograms] using scalar_operations i 0 3

theorem secondAlpha_operations (i : NestedInput) :
    (RationalNestedParametersCode.secondAlpha.runReal (environment i 0)).2 ≤ 128 := by
  simpa [scalarPrograms] using scalar_operations i 0 4

theorem thirdAlpha_operations (i : NestedInput) :
    (RationalNestedParametersCode.thirdAlpha.runReal (environment i 0)).2 ≤ 128 := by
  simpa [scalarPrograms] using scalar_operations i 0 5

end RealNestedParametersCode
namespace ThreeInput

noncomputable def countedRealFormulaWork (i : ThreeInput) : ℕ :=
  if he : 0 < i.a + i.d - i.B then RealThreeGeometryCode.descriptorWork (i.geometry he) else 0

theorem countedRealFormulaWork_bound (i : ThreeInput) : i.countedRealFormulaWork ≤ 2736 := by
  unfold countedRealFormulaWork
  split_ifs
  · exact RealThreeGeometryCode.descriptorWork_bound _
  · exact Nat.zero_le _

end ThreeInput
namespace NestedInput
open RationalNestedParametersCode

noncomputable def realFirstConditionalFormulaWork (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) : ℕ :=
  (RationalNestedParametersCode.conditional.runReal (RealNestedParametersCode.environment i s)).2 +
    if hs : s ∈ i.positiveParameters then
      RealNestedParametersCode.firstParametersWork i s +
        RealThreeGeometryCode.descriptorWork (RealNestedParametersCode.firstGeometry i htv s hs.1 hs.2)
    else 0

theorem realFirstConditionalFormulaWork_bound (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) :
    i.realFirstConditionalFormulaWork htv s ≤ 2928 := by
  have hc := RealNestedParametersCode.conditional_operations i s
  have hp := RealNestedParametersCode.firstParametersWork_bound i s
  unfold realFirstConditionalFormulaWork
  split_ifs with hs
  · have hg := RealThreeGeometryCode.descriptorWork_bound
      (RealNestedParametersCode.firstGeometry i htv s hs.1 hs.2)
    omega
  · omega

noncomputable def realFirstFormulaWork (i : NestedInput) (htv : i.t ≤ i.v) (seed : Fin 10 → ℝ) : ℕ :=
  (RationalNestedParametersCode.location.runReal (RealNestedParametersCode.environment i (seed 0))).2 +
    i.realFirstConditionalFormulaWork htv (RationalNestedParametersCode.location.realValue (RealNestedParametersCode.environment i (seed 0)))

theorem realFirstFormulaWork_bound (i : NestedInput) (htv : i.t ≤ i.v) (seed : Fin 10 → ℝ) :
    i.realFirstFormulaWork htv seed ≤ 3056 := by
  have hl := RealNestedParametersCode.location_operations i (seed 0)
  have hc := i.realFirstConditionalFormulaWork_bound htv
    (RationalNestedParametersCode.location.realValue (RealNestedParametersCode.environment i (seed 0)))
  unfold realFirstFormulaWork
  omega

noncomputable def realFamilyFirstFormulaWork (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxv : x ≤ i.v)
    (seed : Fin 10 → ℝ) : ℕ :=
  (RationalNestedParametersCode.familyProbability.runReal (RealNestedParametersCode.environment i x)).2 +
    (RealNestedParametersCode.atLength i x hx (by linarith [i.lengths.2.2.1])).realFirstFormulaWork hxv seed

theorem realFamilyFirstFormulaWork_bound (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxv : x ≤ i.v)
    (seed : Fin 10 → ℝ) : i.realFamilyFirstFormulaWork x hx hxv seed ≤ 3184 := by
  have hq := RealNestedParametersCode.familyProbability_operations i x
  have hf := (RealNestedParametersCode.atLength i x hx
    (by linarith [i.lengths.2.2.1])).realFirstFormulaWork_bound hxv seed
  unfold realFamilyFirstFormulaWork
  omega

noncomputable def realSecondUniformFormulaWork (i : NestedInput) (htu : i.u ≤ i.t)
    (hTt : i.mirrorLength < i.t) : ℕ :=
  (RationalNestedParametersCode.mirror.runReal (RealNestedParametersCode.environment i 0)).2 +
    (i.secondUniformInput htu hTt).countedRealFormulaWork

theorem realSecondUniformFormulaWork_bound (i : NestedInput) (htu : i.u ≤ i.t)
    (hTt : i.mirrorLength < i.t) : i.realSecondUniformFormulaWork htu hTt ≤ 2864 := by
  have hm := RealNestedParametersCode.mirror_operations i
  have hg := (i.secondUniformInput htu hTt).countedRealFormulaWork_bound
  unfold realSecondUniformFormulaWork
  omega

noncomputable def realSecondFormulaWork (i : NestedInput) (htu : i.u ≤ i.t)
    (seed : Fin 11 → ℝ) : ℕ :=
  (RationalNestedParametersCode.mirror.runReal (RealNestedParametersCode.environment i 0)).2 +
    if hTt : i.mirrorLength < i.t then
      (RationalNestedParametersCode.secondAlpha.runReal (RealNestedParametersCode.environment i 0)).2 +
        if seed 0 ≤ i.secondAlpha then
          i.realFamilyFirstFormulaWork i.mirrorLength (i.mirrorLength_bounds htu).1
            (i.mirrorLength_bounds htu).2.1 (Fin.tail seed)
        else i.realSecondUniformFormulaWork htu hTt
    else i.realFamilyFirstFormulaWork i.mirrorLength (i.mirrorLength_bounds htu).1
      (i.mirrorLength_bounds htu).2.1 (Fin.tail seed)

theorem realSecondFormulaWork_bound (i : NestedInput) (htu : i.u ≤ i.t)
    (seed : Fin 11 → ℝ) : i.realSecondFormulaWork htu seed ≤ 3440 := by
  have hm := RealNestedParametersCode.mirror_operations i
  have ha := RealNestedParametersCode.secondAlpha_operations i
  have hf := i.realFamilyFirstFormulaWork_bound i.mirrorLength (i.mirrorLength_bounds htu).1
    (i.mirrorLength_bounds htu).2.1 (Fin.tail seed)
  unfold realSecondFormulaWork
  split_ifs with hTt hCoin
  · omega
  · have hu := i.realSecondUniformFormulaWork_bound htu hTt
    omega
  · omega

noncomputable def realThirdFormulaWork (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u)
    (seed : Fin 11 → ℝ) : ℕ :=
  if hv : 0 < i.v then
    (RationalNestedParametersCode.thirdAlpha.runReal (RealNestedParametersCode.environment i 0)).2 +
      if seed 0 ≤ i.thirdAlpha then i.realFamilyFirstFormulaWork i.v hv le_rfl (Fin.tail seed)
      else RealNestedResidualCode.descriptorWork (i.residualInput hvt htu)
  else RealNestedResidualCode.descriptorWork (i.residualInput hvt htu)

theorem realThirdFormulaWork_bound (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u)
    (seed : Fin 11 → ℝ) : i.realThirdFormulaWork hvt htu seed ≤ 3312 := by
  have ha := RealNestedParametersCode.thirdAlpha_operations i
  have hr := RealNestedResidualCode.descriptorWork_bound (i.residualInput hvt htu)
  unfold realThirdFormulaWork
  split_ifs with hv hCoin
  · have hf := i.realFamilyFirstFormulaWork_bound i.v hv le_rfl (Fin.tail seed)
    omega
  · omega
  · omega

noncomputable def realFormulaWork (i : NestedInput) (seed : Fin 11 → ℝ) : ℕ :=
  if htv : i.t ≤ i.v then i.realFirstFormulaWork htv (Fin.tail seed) else
    if htu : i.u ≤ i.t then i.realSecondFormulaWork htu seed else
      i.realThirdFormulaWork (lt_of_not_ge htv) (lt_of_not_ge htu) seed

theorem realFormulaWork_bound (i : NestedInput) (seed : Fin 11 → ℝ) : i.realFormulaWork seed ≤ 3440 := by
  unfold realFormulaWork
  split_ifs with htv htu
  · exact (i.realFirstFormulaWork_bound htv _).trans (by decide)
  · exact i.realSecondFormulaWork_bound htu _
  · exact (i.realThirdFormulaWork_bound _ _ _).trans (by decide)

end NestedInput
namespace ThreeSpec

noncomputable def countedRealFormulaWork (i : ThreeSpec) : ℕ :=
  i.orderedInput.countedRealFormulaWork

theorem countedRealFormulaWork_bound (i : ThreeSpec) : i.countedRealFormulaWork ≤ 2736 :=
  i.orderedInput.countedRealFormulaWork_bound

end ThreeSpec
namespace NestedSpec

noncomputable def realFormulaWork (i : NestedSpec) (seed : Fin 11 → ℝ) : ℕ :=
  if hq0 : i.q = 0 then (i.longInput hq0).countedRealFormulaWork else
    if hq1 : i.q = 1 then (i.shortInput hq1).countedRealFormulaWork else
      (i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0))
        (lt_of_le_of_ne i.q_le hq1)).realFormulaWork seed

theorem realFormulaWork_bound (i : NestedSpec) (seed : Fin 11 → ℝ) :
    i.realFormulaWork seed ≤ 3440 := by
  unfold realFormulaWork
  split_ifs with hq0 hq1
  · exact (i.longInput hq0).countedRealFormulaWork_bound.trans (by decide)
  · exact (i.shortInput hq1).countedRealFormulaWork_bound.trans (by decide)
  · exact (i.interiorInput _ _).realFormulaWork_bound seed

end NestedSpec
end Blotto
