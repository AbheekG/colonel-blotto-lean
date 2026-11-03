import Blotto.RationalTerminalResources
import Blotto.RationalNestedProfileBoxes

/-! The native terminal descriptor returns to original coordinate order.
All endpoints satisfy the budget and the original long-coordinate box. -/

namespace Blotto.RationalTerminalResources

theorem endpoint_long (i : RationalTerminalResources) (j : Fin 3) : i.endpoint j ≤ i.long j := by
  unfold endpoint
  split_ifs
  · exact le_rfl
  · exact le_of_lt (i.short_lt j)

theorem permutation_last (i : RationalTerminalResources) : i.permutation 2 = i.focus := by simp [permutation]

theorem permuted_lengths_le (i : RationalTerminalResources) (j : Fin 3) :
    permuteAllocation i.permutation
      ![(i.endpoint (i.permutation 0) : ℝ), (i.endpoint (i.permutation 1) : ℝ), (i.long i.focus : ℝ)] j ≤
        (i.long j : ℝ) := by
  change ![(i.endpoint (i.permutation 0) : ℝ), (i.endpoint (i.permutation 1) : ℝ), (i.long i.focus : ℝ)] (i.permutation j) ≤ _
  by_cases hj : i.permutation j = 2
  · have he : j = i.focus := by
      have h := congrArg i.permutation hj
      simpa [permutation] using h
    rw [hj, he]
    exact le_rfl
  · have hidx : i.permutation j = 0 ∨ i.permutation j = 1 := by
      generalize hk : i.permutation j = k at hj ⊢
      fin_cases k <;> simp_all
    rcases hidx with h0 | h1
    · rw [h0]
      have he := congrArg i.permutation h0
      have hji : j = i.permutation 0 := by simpa [permutation] using he
      change (i.endpoint (i.permutation 0) : ℝ) ≤ (i.long j : ℝ)
      rw [hji]
      exact_mod_cast i.endpoint_long (i.permutation 0)
    · rw [h1]
      have he := congrArg i.permutation h1
      have hji : j = i.permutation 1 := by simpa [permutation] using he
      change (i.endpoint (i.permutation 1) : ℝ) ≤ (i.long j : ℝ)
      rw [hji]
      exact_mod_cast i.endpoint_long (i.permutation 1)

theorem profile_endpoints (i : RationalTerminalResources) (K : ℕ) (outerBits : Fin K → Bool) (slot : Fin 18) :
    FullBudget (i.M : ℝ) ((i.profile K outerBits).real.P slot) ∧
      FullBudget (i.M : ℝ) ((i.profile K outerBits).real.Q slot) := by
  unfold profile
  rw [RationalSegmentLottery.mapped_real]
  have h := i.input.profile_endpoints K outerBits slot
  constructor
  · change FullBudget (i.M : ℝ) ((RationalAffineAllocation.permutation i.permutation).real.value ((i.input.profile K outerBits).real.P slot))
    rw [RationalAffineAllocation.permutation_real]
    exact permuteAllocation_fullBudget i.permutation h.1
  · change FullBudget (i.M : ℝ) ((RationalAffineAllocation.permutation i.permutation).real.value ((i.input.profile K outerBits).real.Q slot))
    rw [RationalAffineAllocation.permutation_real]
    exact permuteAllocation_fullBudget i.permutation h.2

theorem profile_box (i : RationalTerminalResources) (K : ℕ) (outerBits : Fin K → Bool) (slot : Fin 18) :
    InBox (fun j => (i.long j : ℝ)) ((i.profile K outerBits).real.P slot) ∧
      InBox (fun j => (i.long j : ℝ)) ((i.profile K outerBits).real.Q slot) := by
  unfold profile
  rw [RationalSegmentLottery.mapped_real]
  have h := i.input.profile_box K outerBits slot
  constructor
  · change InBox (fun j => (i.long j : ℝ)) ((RationalAffineAllocation.permutation i.permutation).real.value ((i.input.profile K outerBits).real.P slot))
    rw [RationalAffineAllocation.permutation_real]
    exact inBox_mono i.permuted_lengths_le (permuteAllocation_inBox i.permutation h.1)
  · change InBox (fun j => (i.long j : ℝ)) ((RationalAffineAllocation.permutation i.permutation).real.value ((i.input.profile K outerBits).real.Q slot))
    rw [RationalAffineAllocation.permutation_real]
    exact inBox_mono i.permuted_lengths_le (permuteAllocation_inBox i.permutation h.2)

end Blotto.RationalTerminalResources
