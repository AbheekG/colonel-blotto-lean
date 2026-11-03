import Blotto.TerminalLottoLaw
import Blotto.SmallGroupDyadic
import Blotto.ProportionalCDF

/-! Every terminal Lotto resource vector has a finite scalar-draw law with
the common CDF bound and exact budget after grouping/proportional splitting. -/

namespace Blotto.TerminalLotto
open MeasureTheory

noncomputable def uniformDyadicLaw {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) (K : ℕ) : Mixed n :=
  i.partition.splitLaw ((i.uniformSpec h).dyadicLaw i.groups_count K)

theorem uniformDyadicLaw_CDF_error {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) (K : ℕ) :
    CDFClose (i.uniformDyadicLaw h K) (i.uniformLaw h) (3 / (2 * (2 : ℝ) ^ K)) :=
  i.partition.splitLaw_CDFClose _ _ (by positivity) ((i.uniformSpec h).dyadicLaw_CDF_error i.groups_count K)

theorem uniformDyadicLaw_fullBudget {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) (K : ℕ) :
    ∀ᵐ x ∂(i.uniformDyadicLaw h K : Measure (Allocation n)), FullBudget i.B x :=
  i.partition.splitLaw_fullBudget _ ((i.uniformSpec h).dyadicLaw_fullBudget i.groups_count K)

noncomputable def mixedDyadicLaw {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) (K : ℕ) : Mixed n :=
  i.partition.splitMixedLaw pivot ((i.mixedSpec pivot hp).dyadicLaw i.groups_count K)

theorem mixedDyadicLaw_CDF_error {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) (K : ℕ) :
    CDFClose (i.mixedDyadicLaw pivot hp K) (i.mixedLaw pivot hp) (3 / (2 * (2 : ℝ) ^ K)) :=
  i.partition.splitMixedLaw_CDFClose pivot (i.fractional_not_in_groups pivot hp) _ _
    ((i.mixedSpec pivot hp).dyadicLaw_CDF_error i.groups_count K)

theorem mixedDyadicLaw_fullBudget {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) (K : ℕ) :
    ∀ᵐ x ∂(i.mixedDyadicLaw pivot hp K : Measure (Allocation n)), FullBudget i.B x :=
  i.partition.splitMixedLaw_fullBudget pivot _ ((i.mixedSpec pivot hp).dyadicLaw_fullBudget i.groups_count K)

noncomputable def dyadicLaw {n : ℕ} (i : TerminalLotto n) (K : ℕ) : Mixed n := by
  classical
  by_cases h : (fractionalSet i.length i.resource).Nonempty
  · exact i.mixedDyadicLaw h.choose ((mem_fractionalSet _ _ _).mp h.choose_spec) K
  · exact i.uniformDyadicLaw (fun j hj => h ⟨j, (mem_fractionalSet _ _ _).mpr hj⟩) K

theorem dyadicLaw_CDF_error {n : ℕ} (i : TerminalLotto n) (K : ℕ) :
    CDFClose (i.dyadicLaw K) i.law (3 / (2 * (2 : ℝ) ^ K)) := by
  unfold dyadicLaw law
  split_ifs with h
  · exact i.mixedDyadicLaw_CDF_error _ _ K
  · exact i.uniformDyadicLaw_CDF_error _ K

theorem dyadicLaw_fullBudget {n : ℕ} (i : TerminalLotto n) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation n)), FullBudget i.B x := by
  unfold dyadicLaw
  split_ifs with h
  · exact i.mixedDyadicLaw_fullBudget _ _ K
  · exact i.uniformDyadicLaw_fullBudget _ K

end Blotto.TerminalLotto
