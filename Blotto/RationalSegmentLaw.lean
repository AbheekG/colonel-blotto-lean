import Blotto.RationalSegmentProgram
import Blotto.FairBitFiniteAverage
import Blotto.FiniteMixtureOrder
import Blotto.AllocationCDFDistance

/-! The complete two-block rational segment sampler: its actual law, exact
ideal linkage, and dimension-free composition of component-cap and midpoint
errors. The finite support representations appear only in law proofs. -/

namespace Blotto.RationalSegmentLottery
open MeasureTheory Set
open scoped BigOperators

theorem fixedLaw_eq_sample {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R K : ℕ)
    (scalarBits : Fin K → Bool) : l.fixedLaw fallback R K scalarBits =
      (fairBitLaw R).map (fun choiceBits j => (l.sample fallback R K choiceBits scalarBits j : ℝ)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun slot j => (l.point K slot scalarBits j : ℝ))
    (Measure.map ((categoricalMachine fallback).output R l.start fallback) (fairBitLaw R : Measure (Fin R → Bool))) = _
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

noncomputable def cappedLaw {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R K : ℕ) : Mixed n :=
  averagedLaw (fairBitLaw K) (fun scalarBits => l.fixedLaw fallback R K scalarBits) (measurable_of_countable _)

noncomputable def idealMidpointLaw {n k : ℕ} (l : RationalSegmentLottery n k) (K : ℕ) : Mixed n :=
  averagedLaw (fairBitLaw K) (l.fixedIdeal K) (measurable_of_countable _)

theorem idealMidpointLaw_eq {n k : ℕ} (l : RationalSegmentLottery n k) (K : ℕ) :
    l.idealMidpointLaw K = l.real.dyadicLaw K := by
  unfold idealMidpointLaw
  rw [averaged_fairBit_finite]
  unfold fixedIdeal
  rw [probabilityMixture_commute]
  unfold SegmentLottery.dyadicLaw
  congr 1
  funext slot
  have he := averaged_fairBit_finite K (fun scalarBits =>
    allocationPointLaw (fun j => (l.point K slot scalarBits j : ℝ)))
  rw [← he]
  apply ProbabilityMeasure.toMeasure_injective
  change (fairBitLaw K : Measure (Fin K → Bool)).bind
    (fun scalarBits => Measure.dirac (fun j => (l.point K slot scalarBits j : ℝ))) = _
  rw [Measure.bind_dirac_eq_map _ (measurable_of_countable _)]
  change Measure.map (fun scalarBits j => (l.point K slot scalarBits j : ℝ)) (fairBitLaw K : Measure (Fin K → Bool)) =
    Measure.map (dyadicSegmentPoint K (l.real.P slot) (l.real.Q slot)) (fairBitLaw K : Measure (Fin K → Bool))
  congr 1
  exact funext (l.point_real K slot)

theorem cappedLaw_midpoint_CDF_error {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (H K : ℕ) :
    CDFClose (l.cappedLaw fallback (3 * (k - 1 + H)) K) (l.real.dyadicLaw K) (1 / (2 : ℝ) ^ H) := by
  rw [← l.idealMidpointLaw_eq K]
  unfold cappedLaw idealMidpointLaw
  rw [averaged_fairBit_finite, averaged_fairBit_finite]
  apply probabilityMixture_CDFClose
  intro scalarIndex
  exact l.fixedLaw_CDF_error fallback H K ((bitIndexEquiv K).symm scalarIndex)

theorem cappedLaw_CDF_error {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (K : ℕ) :
    CDFClose (l.cappedLaw fallback (3 * (k - 1 + K)) K) l.real.law (3 / (2 * (2 : ℝ) ^ K)) := by
  have h := (l.cappedLaw_midpoint_CDF_error fallback K K).triangle (l.real.dyadicLaw_CDF_error K)
  have hsum : 1 / (2 : ℝ) ^ K + 1 / (2 * (2 : ℝ) ^ K) = 3 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at h
  exact h

theorem cappedLaw_fullBudget {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R K : ℕ)
    {B : ℝ} (h : ∀ slot, FullBudget B (l.real.P slot) ∧ FullBudget B (l.real.Q slot)) :
    ∀ᵐ x ∂(l.cappedLaw fallback R K : Measure (Allocation n)), FullBudget B x := by
  apply averagedLaw_fullBudget
  filter_upwards [] with scalarBits
  rw [l.fixedLaw_eq_sample fallback R K scalarBits]
  change ∀ᵐ x ∂Measure.map (fun choiceBits j => (l.sample fallback R K choiceBits scalarBits j : ℝ))
    (fairBitLaw R : Measure (Fin R → Bool)), FullBudget B x
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (measurable_fullBudget B)]
  exact Filter.Eventually.of_forall (fun choiceBits => l.sample_fullBudget fallback R K h choiceBits scalarBits)

end Blotto.RationalSegmentLottery
