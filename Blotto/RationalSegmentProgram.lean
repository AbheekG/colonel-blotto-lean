import Blotto.RationalCategoricalLaw

/-! Executable selection and rational interpolation for a finite segment
descriptor. Selection uses a single capped fixed-denominator controller;
interpolation uses a separate fresh K-bit midpoint block. Both blocks are
explicit inputs, and no support enumeration occurs in the output function. -/

namespace Blotto.RationalSegmentLottery
open MeasureTheory Set
open scoped BigOperators Classical

def start {n k : ℕ} (l : RationalSegmentLottery n k) : CategoricalState (Fin k) :=
  .remaining (rationalWeightList l.weight l.nonnegative)

def choose {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R : ℕ)
    (bits : Fin R → Bool) : Fin k := (categoricalMachine fallback).output R l.start fallback bits

def sample {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R K : ℕ)
    (choiceBits : Fin R → Bool) (scalarBits : Fin K → Bool) : Fin n → ℚ :=
  l.point K (l.choose fallback R choiceBits) scalarBits

theorem sample_fullBudget {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R K : ℕ)
    {B : ℝ} (h : ∀ slot, FullBudget B (l.real.P slot) ∧ FullBudget B (l.real.Q slot))
    (choiceBits : Fin R → Bool) (scalarBits : Fin K → Bool) :
    FullBudget B (fun j => (l.sample fallback R K choiceBits scalarBits j : ℝ)) :=
  l.point_fullBudget K h _ scalarBits

noncomputable def fixedLaw {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R K : ℕ)
    (scalarBits : Fin K → Bool) : Mixed n :=
  ((categoricalMachine fallback).cappedLaw R l.start fallback).map
    (fun slot j => (l.point K slot scalarBits j : ℝ))

noncomputable def allocationPointLaw {n : ℕ} (x : Allocation n) : Mixed n :=
  ⟨Measure.dirac x, inferInstance⟩

noncomputable def fixedIdeal {n k : ℕ} (l : RationalSegmentLottery n k) (K : ℕ)
    (scalarBits : Fin K → Bool) : Mixed n :=
  probabilityMixture l.real.weight (fun slot =>
    allocationPointLaw (fun j => (l.point K slot scalarBits j : ℝ)))
    l.real.nonnegative l.real.mass

theorem fixedLaw_event_error {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (H K : ℕ)
    (scalarBits : Fin K → Bool) (A : Set (Allocation n)) (hA : MeasurableSet A) :
    |(l.fixedLaw fallback (3 * (k - 1 + H)) K scalarBits : Measure (Allocation n)).real A -
      (l.fixedIdeal K scalarBits : Measure (Allocation n)).real A| ≤ 1 / (2 : ℝ) ^ H := by
  have hm : Measurable (fun slot : Fin k => (fun j => (l.point K slot scalarBits j : ℝ))) := measurable_of_countable _
  have he := rationalCategorical_capped_event l.weight l.nonnegative l.mass fallback H
    ((fun slot j => (l.point K slot scalarBits j : ℝ)) ⁻¹' A)
  have hideal : (l.fixedIdeal K scalarBits : Measure (Allocation n)).real A =
      ∑ slot, (l.weight slot : ℝ) *
        (if (fun j => (l.point K slot scalarBits j : ℝ)) ∈ A then (1 : ℝ) else 0) := by
    unfold fixedIdeal
    rw [probabilityMixture_real_apply _ _ _ _ _ hA]
    apply Finset.sum_congr rfl
    intro slot _
    by_cases hs : (fun j => (l.point K slot scalarBits j : ℝ)) ∈ A <;>
      simp [real, allocationPointLaw, Measure.real, Measure.dirac_apply' _ hA, hs]
  rw [hideal]
  change |(Measure.map (fun slot j => (l.point K slot scalarBits j : ℝ))
    ((categoricalMachine fallback).cappedLaw (3 * (k - 1 + H)) l.start fallback : Measure (Fin k))).real A - _| ≤ _
  rw [Measure.real, Measure.map_apply hm hA]
  exact he

theorem fixedLaw_CDF_error {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (H K : ℕ)
    (scalarBits : Fin K → Bool) :
    CDFClose (l.fixedLaw fallback (3 * (k - 1 + H)) K scalarBits)
      (l.fixedIdeal K scalarBits) (1 / (2 : ℝ) ^ H) := by
  intro j z
  have hA : MeasurableSet {x : Allocation n | x j ≤ z} :=
    (measurable_pi_apply j) measurableSet_Iic
  have he := l.fixedLaw_event_error fallback H K scalarBits {x | x j ≤ z} hA
  change |(Measure.map (fun x : Allocation n => x j)
    (l.fixedLaw fallback (3 * (k - 1 + H)) K scalarBits : Measure (Allocation n))).real (Iic z) -
    (Measure.map (fun x : Allocation n => x j)
    (l.fixedIdeal K scalarBits : Measure (Allocation n))).real (Iic z)| ≤ _
  simp only [Measure.real, Measure.map_apply (measurable_pi_apply j) measurableSet_Iic]
  exact he

end Blotto.RationalSegmentLottery
