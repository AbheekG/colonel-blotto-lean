import Blotto.NestedDyadicCases
import Blotto.NestedSpec
import Blotto.ThreeDyadicCoupling

/-! All positive nested inputs and their endpoint mixture weights have
finite scalar-draw approximations with the common 3/(2*2^K) CDF bound. -/

namespace Blotto
open MeasureTheory

namespace NestedInput

noncomputable def dyadicLaw (i : NestedInput) (K : ℕ) : Mixed 3 :=
  if htv : i.t ≤ i.v then i.firstDyadicApproximation htv K else
    if htu : i.u ≤ i.t then i.secondDyadicLaw htu K else
      i.thirdDyadicLaw (lt_of_not_ge htv) (lt_of_not_ge htu) K

theorem dyadicLaw_CDF_error (i : NestedInput) (K : ℕ) :
    CDFClose (i.dyadicLaw K) i.couplingLaw (3 / (2 * (2 : ℝ) ^ K)) := by
  unfold dyadicLaw couplingLaw
  split_ifs with htv htu
  · exact i.firstDyadicApproximation_CDF_error htv K
  · exact i.secondDyadicLaw_CDF_error htu K
  · exact i.thirdDyadicLaw_CDF_error (lt_of_not_ge htv) (lt_of_not_ge htu) K

theorem dyadicLaw_fullBudget (i : NestedInput) (K : ℕ) :
    ∀ᵐ y ∂(i.dyadicLaw K : Measure (Allocation 3)), FullBudget i.M y := by
  unfold dyadicLaw
  split_ifs with htv htu
  · exact i.firstDyadicApproximation_fullBudget htv K
  · exact i.secondDyadicLaw_fullBudget htu K
  · exact i.thirdDyadicLaw_fullBudget (lt_of_not_ge htv) (lt_of_not_ge htu) K

end NestedInput

namespace NestedSpec

noncomputable def dyadicLaw (i : NestedSpec) (K : ℕ) : Mixed 3 :=
  if hq0 : i.q = 0 then (i.longInput hq0).dyadicLaw K else
    if hq1 : i.q = 1 then (i.shortInput hq1).dyadicLaw K else
      let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
      if i.a ≤ i.d then j.dyadicLaw K else swapLaw (j.dyadicLaw K)

theorem dyadicLaw_CDF_error (i : NestedSpec) (K : ℕ) :
    CDFClose (i.dyadicLaw K) i.law (3 / (2 * (2 : ℝ) ^ K)) := by
  have hδ : 1 / (2 * (2 : ℝ) ^ K) ≤ 3 / (2 * (2 : ℝ) ^ K) :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  unfold dyadicLaw law
  split_ifs with hq0 hq1 had
  · exact ((i.longInput hq0).dyadicLaw_CDF_error K).mono hδ
  · exact ((i.shortInput hq1).dyadicLaw_CDF_error K).mono hδ
  · exact (i.interiorInput _ _).dyadicLaw_CDF_error K
  · exact swapLaw_CDFClose ((i.interiorInput _ _).dyadicLaw_CDF_error K)

theorem dyadicLaw_fullBudget (i : NestedSpec) (K : ℕ) :
    ∀ᵐ y ∂(i.dyadicLaw K : Measure (Allocation 3)), FullBudget i.M y := by
  unfold dyadicLaw
  split_ifs with hq0 hq1 had
  · exact (i.longInput hq0).dyadicLaw_fullBudget K
  · exact (i.shortInput hq1).dyadicLaw_fullBudget K
  · exact (i.interiorInput _ _).dyadicLaw_fullBudget K
  · exact swapLaw_fullBudget ((i.interiorInput _ _).dyadicLaw_fullBudget K)

end NestedSpec
end Blotto
