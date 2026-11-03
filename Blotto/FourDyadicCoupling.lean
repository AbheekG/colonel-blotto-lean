import Blotto.FourReflectionRecovery
import Blotto.GluingDyadicCoupling
import Blotto.NestedResourceDyadic
import Blotto.FourDyadicTransport
import Blotto.FourSpec

/-! Both four-variable branches with finite scalar draws. The reflected
resource law is inside its original box, so subtraction remains nonnegative.
The common CDF error is 3/(2*2^K); all branch probabilities remain exact. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

namespace FourInput

noncomputable def reflectedZeroDyadicLaw (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) : Mixed 4 :=
  reflectedLaw i.originalLengths ((i.reflectedResourceSystem hcase).dyadicLaw K)

theorem reflectedZeroDyadicLaw_CDF_error (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    CDFClose (i.reflectedZeroDyadicLaw hcase K) (i.reflectedZeroLaw hcase) (3 / (2 * (2 : ℝ) ^ K)) :=
  reflectedLaw_CDFClose _ ((i.reflectedResourceSystem hcase).dyadicLaw_CDF_error K)

theorem reflectedZeroDyadicLaw_fullBudget (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    ∀ᵐ x ∂(i.reflectedZeroDyadicLaw hcase K : Measure (Allocation 4)), FullBudget i.B x := by
  have hS : ∑ j, i.originalLengths j = i.B + i.reflectedBudget := by
    rw [i.originalLengths_sum, (i.reflected_budget_bounds hcase).2]
    ring
  exact reflectedLaw_fullBudget _ _ hS ((i.reflectedResourceSystem hcase).dyadicLaw_fullBudget K)
    ((i.reflectedResourceSystem hcase).dyadicLaw_inBox K)

noncomputable def smallUniformDyadicLaw (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) : Mixed 4 :=
  (i.smallUniformInput hcase).dyadicLaw K

theorem smallUniformDyadicLaw_CDF_error (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    CDFClose (i.smallUniformDyadicLaw hcase K) (i.smallUniformLaw hcase) (3 / (2 * (2 : ℝ) ^ K)) :=
  ((i.smallUniformInput hcase).dyadicLaw_CDF_error K).mono
    (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (by positivity))

theorem smallUniformDyadicLaw_fullBudget (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    ∀ᵐ x ∂(i.smallUniformDyadicLaw hcase K : Measure (Allocation 4)), FullBudget i.B x :=
  (i.smallUniformInput hcase).dyadicLaw_fullBudget K

noncomputable def smallCaseDyadicLaw (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) : Mixed 4 :=
  binaryLaw i.p ⟨le_of_lt i.p_pos, le_of_lt i.p_lt⟩
    (i.smallUniformDyadicLaw hcase K) (i.reflectedZeroDyadicLaw hcase K)

theorem smallCaseDyadicLaw_CDF_error (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    CDFClose (i.smallCaseDyadicLaw hcase K) (i.smallCaseLaw hcase) (3 / (2 * (2 : ℝ) ^ K)) :=
  binaryLaw_CDFClose _ _ (i.smallUniformDyadicLaw_CDF_error hcase K) (i.reflectedZeroDyadicLaw_CDF_error hcase K)

theorem smallCaseDyadicLaw_fullBudget (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    ∀ᵐ x ∂(i.smallCaseDyadicLaw hcase K : Measure (Allocation 4)), FullBudget i.B x :=
  binaryLaw_fullBudget _ _ _ _ (i.smallUniformDyadicLaw_fullBudget hcase K) (i.reflectedZeroDyadicLaw_fullBudget hcase K)

noncomputable def dyadicLaw (i : FourInput) (K : ℕ) : Mixed 4 :=
  if hcase : (1 - i.p) * i.ell ≤ i.w then i.gluingDyadicLaw hcase K else
    i.smallCaseDyadicLaw (lt_of_not_ge hcase) K

theorem dyadicLaw_CDF_error (i : FourInput) (K : ℕ) :
    CDFClose (i.dyadicLaw K) i.law (3 / (2 * (2 : ℝ) ^ K)) := by
  unfold dyadicLaw law
  split_ifs with hcase
  · exact (i.gluingDyadicLaw_CDF_error hcase K).mono
      (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (by positivity))
  · exact i.smallCaseDyadicLaw_CDF_error (lt_of_not_ge hcase) K

theorem dyadicLaw_fullBudget (i : FourInput) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation 4)), FullBudget i.B x := by
  unfold dyadicLaw
  split_ifs with hcase
  · exact i.gluingDyadicLaw_fullBudget hcase K
  · exact i.smallCaseDyadicLaw_fullBudget (lt_of_not_ge hcase) K

end FourInput

namespace FourSpec

noncomputable def dyadicLaw (i : FourSpec) (K : ℕ) : Mixed 4 :=
  permuteLaw (permutationWithLast (sortTriplePermutation i.length)).symm (i.input.dyadicLaw K)

theorem dyadicLaw_CDF_error (i : FourSpec) (K : ℕ) :
    CDFClose (i.dyadicLaw K) i.law (3 / (2 * (2 : ℝ) ^ K)) :=
  permuteLaw_CDFClose (i.input.dyadicLaw_CDF_error K) _

theorem dyadicLaw_fullBudget (i : FourSpec) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation 4)), FullBudget i.B x :=
  permuteLaw_fullBudget _ (i.input.dyadicLaw_fullBudget K)

end FourSpec
end Blotto
