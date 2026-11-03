import Blotto.RationalNestedResourceMachine
import Blotto.WordTreeFiniteAverage
import Blotto.RationalSegmentIdealEvent

/-! The serial resource/segment runtime's actual fixed-block law is linked
to its ideal continuation law. Its entire adaptive coin chain has one cap. -/

namespace Blotto.RationalNestedResourceSystem
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def fixedLaw (i : RationalNestedResourceSystem) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) : Mixed 3 :=
  (fairBitLaw R).map (fun choiceBits j => (i.fixedSample K R outerBits scalarBits choiceBits j : ℝ))

noncomputable def fixedIdealLaw (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool) : Mixed 3 :=
  ((i.machine K outerBits scalarBits).specification i.samplingStart).evalLaw
    (fun x => RationalSegmentLottery.allocationPointLaw (fun j => (x j : ℝ)))

theorem fixedIdealLaw_event (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (A : Set (Allocation 3)) (hA : MeasurableSet A) :
    (i.fixedIdealLaw K outerBits scalarBits : Measure (Allocation 3)).real A =
      ((i.machine K outerBits scalarBits).specification i.samplingStart).decode.mean
        (fun x => if (fun j => (x j : ℝ)) ∈ A then (1 : ℝ) else 0) := by
  rw [fixedIdealLaw, WordChoiceTree.evalLaw_real_event _ _ A hA]
  congr 1
  funext x
  by_cases hx : (fun j => (x j : ℝ)) ∈ A <;>
    simp [RationalSegmentLottery.allocationPointLaw, Measure.real, Measure.dirac_apply' _ hA, hx]

theorem fixedIdealLaw_eq (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    i.fixedIdealLaw K outerBits scalarBits = (i.phase.specification i.start).evalLaw
      (fun s => ((i.terminalData s).profile K outerBits).fixedIdeal K scalarBits) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (i.fixedIdealLaw K outerBits scalarBits : Measure (Allocation 3)).real A =
    ((i.phase.specification i.start).evalLaw (fun s => ((i.terminalData s).profile K outerBits).fixedIdeal K scalarBits) : Measure (Allocation 3)).real A
  rw [i.fixedIdealLaw_event K outerBits scalarBits A hA, i.machine_mean, WordChoiceTree.evalLaw_real_event _ _ A hA]
  congr 1
  funext s
  exact (((i.terminalData s).profile K outerBits).fixedIdeal_event K scalarBits A hA).symm

theorem fixedLaw_eq_map (i : RationalNestedResourceSystem) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) :
    i.fixedLaw K R outerBits scalarBits =
      ((i.machine K outerBits scalarBits).cappedLaw R i.samplingStart (i.fallback K outerBits scalarBits)).map
        (fun x : Fin 3 → ℚ => (fun j => (x j : ℝ))) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits j => (i.fixedSample K R outerBits scalarBits bits j : ℝ)) (fairBitLaw R : Measure (Fin R → Bool)) =
    Measure.map (fun x : Fin 3 → ℚ => (fun j => (x j : ℝ)))
      (Measure.map ((i.machine K outerBits scalarBits).output R i.samplingStart (i.fallback K outerBits scalarBits))
        (fairBitLaw R : Measure (Fin R → Bool)))
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

theorem fixedLaw_event_error (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (A : Set (Allocation 3)) (hA : MeasurableSet A) :
    |(i.fixedLaw K (3 * (19 + K)) outerBits scalarBits : Measure (Allocation 3)).real A -
      (i.fixedIdealLaw K outerBits scalarBits : Measure (Allocation 3)).real A| ≤ 1 / (2 : ℝ) ^ K := by
  let castAllocation : (Fin 3 → ℚ) → Allocation 3 := fun x j => (x j : ℝ)
  have hm : Measurable castAllocation := measurable_of_countable _
  have he := (i.machine K outerBits scalarBits).cappedLaw_event_error_precision 19 K i.samplingStart
    (i.machine_rank K outerBits scalarBits) (i.fallback K outerBits scalarBits)
    (castAllocation ⁻¹' A) (hA.preimage hm)
  rw [i.fixedLaw_eq_map, i.fixedIdealLaw_event K outerBits scalarBits A hA]
  change |(Measure.map castAllocation ((i.machine K outerBits scalarBits).cappedLaw (3 * (19 + K))
    i.samplingStart (i.fallback K outerBits scalarBits) : Measure (Fin 3 → ℚ))).real A - _| ≤ _
  rw [map_measureReal_apply hm hA]
  rw [AdaptiveChoiceTree.idealLaw_real_event _ _ (hA.preimage hm)] at he
  exact he

theorem fixedLaw_CDF_error (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    CDFClose (i.fixedLaw K (3 * (19 + K)) outerBits scalarBits) (i.fixedIdealLaw K outerBits scalarBits) (1 / (2 : ℝ) ^ K) := by
  intro j z
  have he := i.fixedLaw_event_error K outerBits scalarBits {x : Allocation 3 | x j ≤ z}
    ((measurable_pi_apply j) measurableSet_Iic)
  change |(Measure.map (fun x : Allocation 3 => x j) (i.fixedLaw K (3 * (19 + K)) outerBits scalarBits : Measure (Allocation 3))).real (Iic z) -
    (Measure.map (fun x : Allocation 3 => x j) (i.fixedIdealLaw K outerBits scalarBits : Measure (Allocation 3))).real (Iic z)| ≤ _
  simp only [Measure.real, Measure.map_apply (measurable_pi_apply j) measurableSet_Iic]
  exact he

theorem averaged_fixedIdeal_inner (i : RationalNestedResourceSystem) (K : ℕ) (outerBits : Fin K → Bool) :
    averagedLaw (fairBitLaw K) (fun scalarBits => i.fixedIdealLaw K outerBits scalarBits) (measurable_of_countable _) =
      (i.phase.specification i.start).evalLaw (fun s => ((i.terminalData s).profile K outerBits).real.dyadicLaw K) := by
  calc
    _ = averagedLaw (fairBitLaw K) (fun bits => (i.phase.specification i.start).evalLaw
        (fun s => ((i.terminalData s).profile K outerBits).fixedIdeal K bits)) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      exact i.fixedIdealLaw_eq K outerBits
    _ = _ := by
      rw [WordChoiceTree.evalLaw_averaged_fairBits]
      congr 1
      funext s
      exact ((i.terminalData s).profile K outerBits).idealMidpointLaw_eq K

theorem averaged_fixedIdeal (i : RationalNestedResourceSystem) (K : ℕ) :
    averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
      (fun scalarBits => i.fixedIdealLaw K outerBits scalarBits) (measurable_of_countable _)) (measurable_of_countable _) =
      i.midpointLaw K := by
  calc
    _ = averagedLaw (fairBitLaw K) (fun outerBits => (i.phase.specification i.start).evalLaw
      (fun s => ((i.terminalData s).profile K outerBits).real.dyadicLaw K)) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      exact i.averaged_fixedIdeal_inner K
    _ = _ := by
      rw [WordChoiceTree.evalLaw_averaged_fairBits]
      rfl

end Blotto.RationalNestedResourceSystem
