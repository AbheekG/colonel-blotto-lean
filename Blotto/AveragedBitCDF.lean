import Blotto.FairBitFiniteAverage
import Blotto.AllocationCDFDistance

/-! Uniform marginal CDF error survives averaging over a fresh finite fair
parameter block. The index-mixture representation is used only in the proof. -/

namespace Blotto
open MeasureTheory

theorem averaged_fairBit_CDFClose {n : ℕ} (K : ℕ) (a b : (Fin K → Bool) → Mixed n) {δ : ℝ}
    (h : ∀ bits, CDFClose (a bits) (b bits) δ) :
    CDFClose (averagedLaw (fairBitLaw K) a (measurable_of_countable _))
      (averagedLaw (fairBitLaw K) b (measurable_of_countable _)) δ := by
  rw [averaged_fairBit_finite, averaged_fairBit_finite]
  apply probabilityMixture_CDFClose
  intro scalarIndex
  exact h ((bitIndexEquiv K).symm scalarIndex)

end Blotto
