import Blotto.RealFirstSampler
import Blotto.NestedFamily
import Blotto.RealNestedFamilyCompiler

/-! First-case execution at a fixed admissible family length. The family
retains the original budget and its already proved conditional law. -/

namespace Blotto.NestedInput
open MeasureTheory

noncomputable def realFamilyFirstSample (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxv : x ≤ i.v)
    (seed : Fin 10 → ℝ) : Allocation 3 :=
  (RealNestedParametersCode.atLength i x hx (by linarith [i.lengths.2.2.1])).realFirstSample hxv seed

theorem realFamilyFirstSample_refines (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxv : x ≤ i.v) :
    i.realFamilyFirstSample x hx hxv =
      (i.atLength x hx (by linarith [i.lengths.2.2.1])).realFirstSample hxv := by
  funext seed
  exact realFirstSample_input_congr _ _ hxv hxv
    (RealNestedParametersCode.atLength_eq i x hx _) seed

theorem realFamilyFirstSample_length_congr (i : NestedInput) (x y : ℝ)
    (hx : 0 < x) (hxv : x ≤ i.v) (hy : 0 < y) (hyv : y ≤ i.v) (hxy : x = y)
    (seed : Fin 10 → ℝ) :
    i.realFamilyFirstSample x hx hxv seed = i.realFamilyFirstSample y hy hyv seed := by
  cases hxy
  rfl

theorem realFamilyFirstSample_measurable (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxv : x ≤ i.v) :
    Measurable (i.realFamilyFirstSample x hx hxv) := by
  rw [i.realFamilyFirstSample_refines]
  exact (i.atLength x hx (by linarith [i.lengths.2.2.1])).realFirstSample_measurable hxv

theorem realFamilyFirstSample_law (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxv : x ≤ i.v) :
    Measure.map (i.realFamilyFirstSample x hx hxv) (RealUniformInputs.law 10 : Measure (Fin 10 → ℝ)) =
      (i.familyFirstLaw x hx hxv : Measure (Allocation 3)) := by
  rw [i.realFamilyFirstSample_refines]
  exact (i.atLength x hx (by linarith [i.lengths.2.2.1])).realFirstSample_law hxv

theorem realFamilyFirstSample_fullBudget (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxv : x ≤ i.v)
    (seed : Fin 10 → ℝ) (hr : 0 ≤ seed 0 ∧ seed 0 ≤ 1) (ht : 0 ≤ seed 1 ∧ seed 1 ≤ 1) :
    FullBudget i.M (i.realFamilyFirstSample x hx hxv seed) := by
  rw [i.realFamilyFirstSample_refines]
  exact (i.atLength x hx (by linarith [i.lengths.2.2.1])).realFirstSample_fullBudget hxv seed hr ht

end Blotto.NestedInput
