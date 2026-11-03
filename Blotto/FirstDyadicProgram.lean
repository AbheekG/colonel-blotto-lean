import Blotto.FirstDyadicApproximation
import Blotto.AverageFairBits

/-! Sequential interpretation of the first nested finite law: K fresh fair
bits choose the location, then the conditional law uses another K-bit scalar
primitive. Conditional component choices still have exact probabilities. -/

namespace Blotto.NestedInput
open MeasureTheory

noncomputable def firstDyadicProgramLaw (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) : Mixed 3 :=
  averagedLaw (fairBitLaw K)
    (fun bits => i.firstConditionalDyadicLaw htv (i.location (dyadicMidpointSample K bits)) K)
    (measurable_of_countable _)

theorem firstDyadicProgramLaw_eq (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    i.firstDyadicProgramLaw htv K = i.firstDyadicApproximation htv K := by
  unfold firstDyadicProgramLaw
  simp_rw [dyadicMidpointSample_real]
  exact averaged_fairBit_indices K (fun j => i.firstConditionalDyadicLaw htv (i.location (midpoint j)) K)

theorem firstDyadicProgramLaw_CDF_error (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    CDFClose (i.firstDyadicProgramLaw htv K) (i.firstLaw htv) (3 / (2 * (2 : ℝ) ^ K)) := by
  rw [i.firstDyadicProgramLaw_eq]
  exact i.firstDyadicApproximation_CDF_error htv K

end Blotto.NestedInput
