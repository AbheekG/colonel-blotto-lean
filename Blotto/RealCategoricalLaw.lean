import Blotto.RealCategoricalMean
import Blotto.RealStateMachineCounts

/-! Exact independent-uniform categorical execution realizes all finite
normalized real tables, including zero entries and unused zero-mass tails. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def realWeightTable {k : ℕ} (weight : Fin k → ℝ) (h : ∀ j, 0 ≤ weight j) : RealWeightList (Fin k) :=
  RealWeightList.prepare (List.ofFn (fun j => (j, weight j))) (by
    intro item hi
    rcases List.mem_ofFn.mp hi with ⟨j, rfl⟩
    exact h j)

theorem realWeightTable_mass {k : ℕ} (weight : Fin k → ℝ) (h : ∀ j, 0 ≤ weight j) :
    (realWeightTable weight h).mass = ∑ j, weight j := by
  simp [realWeightTable, RealWeightList.prepare, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem realWeightTable_weightedSum {k : ℕ} (weight : Fin k → ℝ) (h : ∀ j, 0 ≤ weight j) (f : Fin k → ℝ) :
    (realWeightTable weight h).weightedSum f = ∑ j, weight j * f j := by
  simp [RealWeightList.weightedSum, realWeightTable, RealWeightList.prepare,
    List.map_ofFn, List.sum_ofFn, Function.comp_def]

noncomputable def realCategorical {k : ℕ} (weight : Fin k → ℝ) (h : ∀ j, 0 ≤ weight j) (fallback : Fin k)
    (seed : Fin (k - 1) → ℝ) : Fin k :=
  (realCategoricalMachine fallback).output (k - 1) (.remaining (realWeightTable weight h)) fallback seed

theorem realCategorical_measurable {k : ℕ} (weight : Fin k → ℝ) (h : ∀ j, 0 ≤ weight j) (fallback : Fin k) :
    Measurable (realCategorical weight h fallback) := by
  have he : realCategorical weight h fallback =
      ((realCategoricalMachine fallback).specification (.remaining (realWeightTable weight h))).output (k - 1) fallback :=
    funext ((realCategoricalMachine fallback).output_refines (k - 1) (.remaining (realWeightTable weight h)) fallback)
  rw [he]
  exact RealChoiceTree.measurable_output _ _ _

theorem realCategorical_event {k : ℕ} (weight : Fin k → ℝ) (h : ∀ j, 0 ≤ weight j)
    (hMass : ∑ j, weight j = 1) (fallback : Fin k) (A : Set (Fin k)) :
    (Measure.map (realCategorical weight h fallback) (RealUniformInputs.law (k - 1) : Measure (Fin (k - 1) → ℝ))).real A =
      ∑ j, weight j * (if j ∈ A then (1 : ℝ) else 0) := by
  have hm : (realWeightTable weight h).mass = 1 := (realWeightTable_mass weight h).trans hMass
  have hRank : (realCategoricalMachine fallback).rank (.remaining (realWeightTable weight h)) ≤ k - 1 := by
    simp [realCategoricalMachine, realCategoricalRank, realWeightTable, RealWeightList.prepare]
  change (Measure.map ((realCategoricalMachine fallback).output (k - 1)
    (.remaining (realWeightTable weight h)) fallback) (RealUniformInputs.law (k - 1) : Measure (Fin (k - 1) → ℝ))).real A = _
  rw [(realCategoricalMachine fallback).output_law _ _ _ hRank,
    RealChoiceTree.idealLaw_real_event _ A (Set.toFinite A).measurableSet]
  rw [realCategoricalMachine_mean fallback _ _ (by rw [hm]; norm_num), hm, div_one,
    realWeightTable_weightedSum]

theorem realCategorical_calls {k : ℕ} (weight : Fin k → ℝ) (h : ∀ j, 0 ≤ weight j)
    (fallback : Fin k) (seed : Fin (k - 1) → ℝ) :
    (realCategoricalMachine fallback).visits (k - 1) seed (.remaining (realWeightTable weight h)) 0 (Nat.zero_le _) ≤ (k - 1) + 1 := by
  have hCalls := (realCategoricalMachine fallback).visits_bound (k - 1) seed (.remaining (realWeightTable weight h)) 0 (Nat.zero_le _)
  simpa [realCategoricalMachine, realCategoricalRank, realWeightTable, RealWeightList.prepare] using hCalls

theorem realCategorical_law {k : ℕ} (weight : Fin k → ℝ) (h : ∀ j, 0 ≤ weight j)
    (hMass : ∑ j, weight j = 1) (fallback : Fin k) :
    Measure.map (realCategorical weight h fallback) (RealUniformInputs.law (k - 1) : Measure (Fin (k - 1) → ℝ)) =
      (probabilityMixture weight (fun j => RealThresholdChoice.pointLaw j) h hMass : Measure (Fin k)) := by
  apply Measure.ext
  intro A hA
  have hReal : (Measure.map (realCategorical weight h fallback)
      (RealUniformInputs.law (k - 1) : Measure (Fin (k - 1) → ℝ))).real A =
      (probabilityMixture weight (fun j => RealThresholdChoice.pointLaw j) h hMass : Measure (Fin k)).real A := by
    rw [realCategorical_event weight h hMass fallback A, probabilityMixture_real_apply _ _ _ _ _ hA]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ A <;> simp [RealThresholdChoice.pointLaw, Measure.real, Measure.dirac_apply' _ hA, hj]
  have hEq := congrArg ENNReal.ofReal hReal
  rw [ofReal_measureReal (measure_ne_top _ _), ofReal_measureReal (measure_ne_top _ _)] at hEq
  exact hEq

end Blotto
