import Blotto.DyadicSegmentLottery
import Blotto.NestedBoxes

/-! Coordinate boxes for finite scalar-draw laws, with translation and
mixture support. These ensure later reflection remains nonnegative. -/

namespace Blotto
open MeasureTheory Set

namespace SegmentLottery

theorem dyadicLaw_inBox {n k : ℕ} (l : SegmentLottery n k) (K : ℕ) {L : Allocation n}
    (h : ∀ j, InBox L (l.P j) ∧ InBox L (l.Q j)) :
    ∀ᵐ x ∂(l.dyadicLaw K : Measure (Allocation n)), InBox L x := by
  apply probabilityMixture_ae
  intro j
  rw [dyadicSegmentLaw_eq]
  exact midpointSegmentLaw_inBox _ (h j).1 (h j).2

theorem dyadicPoint_inBox {n k : ℕ} (l : SegmentLottery n k) (K : ℕ) {L : Allocation n}
    (h : ∀ j, InBox L (l.P j) ∧ InBox L (l.Q j)) (j : Fin k) (bits : Fin K → Bool) :
    InBox L (l.dyadicPoint K j bits) :=
  segment_inBox (h j).1 (h j).2 ⟨le_of_lt (dyadicMidpointSample_bounds K bits).1,
    le_of_lt (dyadicMidpointSample_bounds K bits).2⟩

end SegmentLottery

theorem shiftedLaw_inBox {μ : Mixed 3} {a d c s : ℝ} (hs : 0 ≤ s)
    (hμ : ∀ᵐ x ∂(μ : Measure (Allocation 3)), InBox ![a, d, c] x) :
    ∀ᵐ x ∂(shiftedLaw s μ : Measure (Allocation 3)), InBox ![a, d, c + s] x := by
  change ∀ᵐ x ∂Measure.map (shiftThird s) (μ : Measure (Allocation 3)), InBox ![a, d, c + s] x
  rw [ae_map_iff (measurable_shiftThird s).aemeasurable (measurable_inBox _)]
  exact hμ.mono (fun _ hx => shiftThird_inBox hs hx)

theorem binaryLaw_inBox {n : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (μ ν : Mixed n) {L : Allocation n}
    (hμ : ∀ᵐ x ∂(μ : Measure (Allocation n)), InBox L x)
    (hν : ∀ᵐ x ∂(ν : Measure (Allocation n)), InBox L x) :
    ∀ᵐ x ∂(binaryLaw p hp μ ν : Measure (Allocation n)), InBox L x := by
  apply probabilityMixture_ae
  intro j
  fin_cases j
  · exact hμ
  · exact hν

theorem swapLaw_inBox {μ : Mixed 3} {a d c : ℝ}
    (hμ : ∀ᵐ x ∂(μ : Measure (Allocation 3)), InBox ![a, d, c] x) :
    ∀ᵐ x ∂(swapLaw μ : Measure (Allocation 3)), InBox ![d, a, c] x := by
  change ∀ᵐ x ∂Measure.map swapFirst (μ : Measure (Allocation 3)), InBox ![d, a, c] x
  rw [ae_map_iff measurable_swapFirst.aemeasurable (measurable_inBox _)]
  apply hμ.mono
  intro x hx j
  fin_cases j
  · exact hx 1
  · exact hx 0
  · exact hx 2

end Blotto
