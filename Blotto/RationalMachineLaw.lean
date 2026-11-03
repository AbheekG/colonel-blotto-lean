import Blotto.WordTreeFiniteAverage
import Blotto.RationalSegmentIdealEvent
import Blotto.WordMachineMap

/-! Generic allocation-law contracts for a native rational-output controller.
Every adaptive request uses the same cap, and the cap error holds for any
measurable real-allocation event after decoding the rational output. -/

namespace Blotto
open MeasureTheory Set
open scoped Classical

namespace WordChoiceTree

theorem map_forLeaves {α β : Type*} (T : WordChoiceTree α) (f : α → β) (P : β → Prop)
    (h : T.decode.ForLeaves (fun x => P (f x))) : (T.map f).decode.ForLeaves P := by
  induction T with
  | leaf x => exact h
  | fork a b hb hab upper lower hu hl => exact ⟨hu h.1, hl h.2⟩

end WordChoiceTree

namespace WordStateMachine

noncomputable def rationalIdealLaw {S : Type*} {n : ℕ} (m : WordStateMachine S (Fin n → ℚ)) (s : S) : Mixed n :=
  (m.specification s).evalLaw (fun x => RationalSegmentLottery.allocationPointLaw (fun j => (x j : ℝ)))

noncomputable def rationalCappedLaw {S : Type*} {n : ℕ} (m : WordStateMachine S (Fin n → ℚ)) (R : ℕ)
    (s : S) (fallback : Fin n → ℚ) : Mixed n :=
  (fairBitLaw R).map (fun bits j => (m.output R s fallback bits j : ℝ))

theorem rationalIdealLaw_event {S : Type*} {n : ℕ} (m : WordStateMachine S (Fin n → ℚ)) (s : S)
    (A : Set (Allocation n)) (hA : MeasurableSet A) :
    (m.rationalIdealLaw s : Measure (Allocation n)).real A =
      (m.specification s).decode.mean (fun x => if (fun j => (x j : ℝ)) ∈ A then (1 : ℝ) else 0) := by
  rw [rationalIdealLaw, WordChoiceTree.evalLaw_real_event _ _ A hA]
  congr 1
  funext x
  by_cases hx : (fun j => (x j : ℝ)) ∈ A <;>
    simp [RationalSegmentLottery.allocationPointLaw, Measure.real, Measure.dirac_apply' _ hA, hx]

theorem rationalCappedLaw_eq_map {S : Type*} {n : ℕ} (m : WordStateMachine S (Fin n → ℚ)) (R : ℕ)
    (s : S) (fallback : Fin n → ℚ) :
    m.rationalCappedLaw R s fallback = (m.cappedLaw R s fallback).map
      (fun x : Fin n → ℚ => (fun j => (x j : ℝ))) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits j => (m.output R s fallback bits j : ℝ)) (fairBitLaw R : Measure (Fin R → Bool)) =
    Measure.map (fun x : Fin n → ℚ => (fun j => (x j : ℝ)))
      (Measure.map (m.output R s fallback) (fairBitLaw R : Measure (Fin R → Bool)))
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

theorem rationalCappedLaw_event_error {S : Type*} {n : ℕ} (m : WordStateMachine S (Fin n → ℚ)) (C K : ℕ)
    (s : S) (hs : m.rank s ≤ C) (fallback : Fin n → ℚ) (A : Set (Allocation n)) (hA : MeasurableSet A) :
    |(m.rationalCappedLaw (3 * (C + K)) s fallback : Measure (Allocation n)).real A -
      (m.rationalIdealLaw s : Measure (Allocation n)).real A| ≤ 1 / (2 : ℝ) ^ K := by
  let castAllocation : (Fin n → ℚ) → Allocation n := fun x j => (x j : ℝ)
  have hm : Measurable castAllocation := measurable_of_countable _
  have h := m.cappedLaw_event_error_precision C K s hs fallback (castAllocation ⁻¹' A) (hA.preimage hm)
  rw [m.rationalCappedLaw_eq_map, m.rationalIdealLaw_event s A hA]
  change |(Measure.map castAllocation (m.cappedLaw (3 * (C + K)) s fallback : Measure (Fin n → ℚ))).real A - _| ≤ _
  rw [map_measureReal_apply hm hA]
  rw [AdaptiveChoiceTree.idealLaw_real_event _ _ (hA.preimage hm)] at h
  exact h

theorem rationalCappedLaw_CDF_error {S : Type*} {n : ℕ} (m : WordStateMachine S (Fin n → ℚ)) (C K : ℕ)
    (s : S) (hs : m.rank s ≤ C) (fallback : Fin n → ℚ) :
    CDFClose (m.rationalCappedLaw (3 * (C + K)) s fallback) (m.rationalIdealLaw s) (1 / (2 : ℝ) ^ K) := by
  intro j z
  have h := m.rationalCappedLaw_event_error C K s hs fallback {x : Allocation n | x j ≤ z}
    ((measurable_pi_apply j) measurableSet_Iic)
  change |(Measure.map (fun x : Allocation n => x j) (m.rationalCappedLaw (3 * (C + K)) s fallback : Measure (Allocation n))).real (Iic z) -
    (Measure.map (fun x : Allocation n => x j) (m.rationalIdealLaw s : Measure (Allocation n))).real (Iic z)| ≤ _
  simp only [Measure.real, Measure.map_apply (measurable_pi_apply j) measurableSet_Iic]
  exact h

end WordStateMachine
end Blotto
