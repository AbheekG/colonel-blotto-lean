import Blotto.RationalCategoricalMean
import Blotto.RationalSegmentLottery
import Mathlib.Algebra.BigOperators.Fin

/-! Native enumeration of rational categorical weights. The controller's
ideal law is exactly the finite weighted measure, and its actual shared-cap
output differs on every event by at most the proved exhaustion bound. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators Classical

def rationalWeightList {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ i, 0 ≤ weight i) : RationalWeightList (Fin k) where
  items := List.ofFn (fun i => (i, weight i))
  nonnegative := by
    intro item hi
    rcases List.mem_ofFn.mp hi with ⟨i, rfl⟩
    exact hw i

theorem rationalWeightList_mass {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ i, 0 ≤ weight i) :
    (rationalWeightList weight hw).mass = ∑ i, weight i := by
  simp [rationalWeightList, RationalWeightList.mass, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem rationalWeightList_weightedSum {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ i, 0 ≤ weight i) (f : Fin k → ℝ) :
    (rationalWeightList weight hw).weightedSum f = ∑ i, (weight i : ℝ) * f i := by
  simp [rationalWeightList, RationalWeightList.weightedSum, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem rationalCategorical_mean {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ i, 0 ≤ weight i)
    (hs : ∑ i, weight i = 1) (fallback : Fin k) (f : Fin k → ℝ) :
    ((categoricalMachine fallback).specification (.remaining (rationalWeightList weight hw))).decode.mean f =
      ∑ i, (weight i : ℝ) * f i := by
  have hm : (rationalWeightList weight hw).mass = 1 := by rw [rationalWeightList_mass, hs]
  rw [categoricalMachine_mean fallback f _ (by rw [hm]; norm_num), hm,
    Rat.cast_one, div_one, rationalWeightList_weightedSum]

theorem rationalCategorical_ideal_event {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ i, 0 ≤ weight i)
    (hs : ∑ i, weight i = 1) (fallback : Fin k) (A : Set (Fin k)) :
    ((((categoricalMachine fallback).specification (.remaining (rationalWeightList weight hw))).decode.idealLaw : Measure (Fin k)).real A) =
      ∑ i, (weight i : ℝ) * (if i ∈ A then (1 : ℝ) else 0) := by
  rw [AdaptiveChoiceTree.idealLaw_real_event _ _ (Set.toFinite A).measurableSet,
    rationalCategorical_mean weight hw hs]

theorem rationalCategorical_capped_event {k : ℕ} (weight : Fin k → ℚ) (hw : ∀ i, 0 ≤ weight i)
    (hs : ∑ i, weight i = 1) (fallback : Fin k) (K : ℕ) (A : Set (Fin k)) :
    |((categoricalMachine fallback).cappedLaw (3 * (k - 1 + K))
        (.remaining (rationalWeightList weight hw)) fallback : Measure (Fin k)).real A -
      ∑ i, (weight i : ℝ) * (if i ∈ A then (1 : ℝ) else 0)| ≤ 1 / (2 : ℝ) ^ K := by
  rw [← rationalCategorical_ideal_event weight hw hs fallback A]
  apply (categoricalMachine fallback).cappedLaw_event_error_precision (k - 1) K
    (.remaining (rationalWeightList weight hw)) _ fallback A (Set.toFinite A).measurableSet
  simp [categoricalMachine, categoricalRank, rationalWeightList]

end Blotto
