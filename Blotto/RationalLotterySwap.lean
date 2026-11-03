import Blotto.RationalLotteryAssembly
import Blotto.AveragedBitMixtures

/-! Native coordinate swapping of a segment descriptor and commutation with
a finite parameter average. Whole laws and all endpoint budgets are preserved. -/

namespace Blotto
open MeasureTheory

namespace RationalSegmentLottery

def swapFirst {k : ℕ} (l : RationalSegmentLottery 3 k) : RationalSegmentLottery 3 k :=
  ⟨l.weight, (fun slot => ![l.P slot 1, l.P slot 0, l.P slot 2]),
    (fun slot => ![l.Q slot 1, l.Q slot 0, l.Q slot 2]), l.nonnegative, l.mass⟩

theorem swapFirst_real {k : ℕ} (l : RationalSegmentLottery 3 k) :
    l.swapFirst.real = l.real.mapped AffineAllocation.swapFirst := by
  apply SegmentLottery.eq_of_fields
  · rfl
  · funext slot j
    fin_cases j <;> rfl
  · funext slot j
    fin_cases j <;> rfl

theorem swapFirst_law {k : ℕ} (l : RationalSegmentLottery 3 k) : l.swapFirst.real.law = swapLaw l.real.law := by
  rw [l.swapFirst_real]
  apply ProbabilityMeasure.toMeasure_injective
  exact l.real.mapped_law AffineAllocation.swapFirst

theorem swapFirst_endpoints {k : ℕ} (l : RationalSegmentLottery 3 k) {B : ℝ}
    (h : ∀ slot, FullBudget B (l.real.P slot) ∧ FullBudget B (l.real.Q slot)) :
    ∀ slot, FullBudget B (l.swapFirst.real.P slot) ∧ FullBudget B (l.swapFirst.real.Q slot) := by
  rw [l.swapFirst_real]
  intro slot
  exact ⟨swapFirst_fullBudget (h slot).1, swapFirst_fullBudget (h slot).2⟩

end RationalSegmentLottery

theorem averaged_fairBit_swap (K : ℕ) (law : (Fin K → Bool) → Mixed 3) :
    averagedLaw (fairBitLaw K) (fun bits => swapLaw (law bits)) (measurable_of_countable _) =
      swapLaw (averagedLaw (fairBitLaw K) law (measurable_of_countable _)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (fairBitLaw K : Measure (Fin K → Bool)).bind
    (fun bits => Measure.map Blotto.swapFirst (law bits : Measure (Allocation 3))) =
    Measure.map Blotto.swapFirst ((fairBitLaw K : Measure (Fin K → Bool)).bind (fun bits => (law bits : Measure (Allocation 3))))
  exact (map_bind_family _ _ (measurable_of_countable _) Blotto.swapFirst measurable_swapFirst).symm

end Blotto
