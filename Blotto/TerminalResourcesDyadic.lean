import Blotto.TerminalResources
import Blotto.NestedDyadicPaths

/-! The terminal nested-resource law retains its dyadic CDF bound under the
coordinate permutation and remains inside the original coordinate box. -/

namespace Blotto
open MeasureTheory Set

theorem permuteLaw_inBox {n : ℕ} (π : Equiv.Perm (Fin n)) (μ : Mixed n) {L : Allocation n}
    (hμ : ∀ᵐ x ∂(μ : Measure (Allocation n)), InBox L x) :
    ∀ᵐ x ∂(permuteLaw π μ : Measure (Allocation n)), InBox (permuteAllocation π L) x := by
  change ∀ᵐ x ∂Measure.map (permuteAllocation π) (μ : Measure (Allocation n)), InBox (permuteAllocation π L) x
  rw [ae_map_iff (measurable_permuteAllocation π).aemeasurable (measurable_inBox _)]
  exact hμ.mono (fun _ hx => permuteAllocation_inBox π hx)

namespace TerminalResources

noncomputable def dyadicLaw (i : TerminalResources) (K : ℕ) : Mixed 3 :=
  permuteLaw i.permutation (i.input.dyadicLaw K)

theorem dyadicLaw_CDF_error (i : TerminalResources) (K : ℕ) :
    CDFClose (i.dyadicLaw K) i.law (3 / (2 * (2 : ℝ) ^ K)) :=
  permuteLaw_CDFClose (i.input.dyadicLaw_CDF_error K) i.permutation

theorem dyadicLaw_fullBudget (i : TerminalResources) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation 3)), FullBudget i.M x :=
  permuteLaw_fullBudget i.permutation (i.input.dyadicLaw_fullBudget K)

theorem permutedInput_bounds (i : TerminalResources) :
    ∀ j, permuteAllocation i.permutation ![i.input.a, i.input.d, i.input.c] j ≤ i.long j := by
  intro j
  change ![i.endpoint (i.permutation 0), i.endpoint (i.permutation 1), i.long i.focus] (i.permutation j) ≤ i.long j
  by_cases hj : i.permutation j = 2
  · have he : j = i.focus := by
      have he := congrArg i.permutation hj
      simpa [permutation] using he
    rw [hj, he]
    exact le_rfl
  · have hidx : i.permutation j = 0 ∨ i.permutation j = 1 := by
      generalize he : i.permutation j = k at hj ⊢
      fin_cases k <;> simp_all
    rcases hidx with h0 | h1
    · rw [h0]
      have he := congrArg i.permutation h0
      have hji : j = i.permutation 0 := by simpa [permutation] using he
      simpa [hji] using i.endpoint_long (i.permutation 0)
    · rw [h1]
      have he := congrArg i.permutation h1
      have hji : j = i.permutation 1 := by simpa [permutation] using he
      simpa [hji] using i.endpoint_long (i.permutation 1)

theorem dyadicLaw_inBox (i : TerminalResources) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation 3)), InBox i.long x :=
  (permuteLaw_inBox i.permutation _ (i.input.dyadicLaw_inBox K)).mono
    (fun _ hx => inBox_mono i.permutedInput_bounds hx)

end TerminalResources
end Blotto
