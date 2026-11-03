import Blotto.FairBitFiniteAverage
import Blotto.FiniteMixtureOrder
import Blotto.BinaryMixture

/-! A finite fair parameter block commutes with a fixed binary mixture.
These are whole-law identities for independent draws, including p=0/1. -/

namespace Blotto
open MeasureTheory

theorem averaged_fairBit_congr {n : ℕ} (K : ℕ) (a b : (Fin K → Bool) → Mixed n)
    (h : ∀ bits, a bits = b bits) :
    averagedLaw (fairBitLaw K) a (measurable_of_countable _) =
      averagedLaw (fairBitLaw K) b (measurable_of_countable _) := by
  have he : a = b := funext h
  cases he
  rfl

theorem averaged_fairBit_constant {n : ℕ} (K : ℕ) (law : Mixed n) :
    averagedLaw (fairBitLaw K) (fun _ => law) (measurable_of_countable _) = law := by
  apply ProbabilityMeasure.toMeasure_injective
  change (fairBitLaw K : Measure (Fin K → Bool)).bind (fun _ => (law : Measure (Allocation n))) = _
  rw [Measure.bind_const, measure_univ, one_smul]

theorem averaged_fairBit_binary {n : ℕ} (K : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (a b : (Fin K → Bool) → Mixed n) :
    averagedLaw (fairBitLaw K) (fun bits => binaryLaw p hp (a bits) (b bits)) (measurable_of_countable _) =
      binaryLaw p hp (averagedLaw (fairBitLaw K) a (measurable_of_countable _))
        (averagedLaw (fairBitLaw K) b (measurable_of_countable _)) := by
  rw [averaged_fairBit_finite]
  unfold binaryLaw
  rw [probabilityMixture_commute]
  congr 1
  funext flag
  fin_cases flag
  · exact (averaged_fairBit_finite K a).symm
  · exact (averaged_fairBit_finite K b).symm

end Blotto
