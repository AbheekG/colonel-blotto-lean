import Blotto.SmallGroupLaws
import Blotto.FourDyadicCoupling

/-! Finite scalar draws for two/three uniform groups and the optional final
zero/uniform coordinate. The bound is uniform over all grouped lengths. -/

namespace Blotto
open MeasureTheory

noncomputable def complementaryPairDyadicLaw (B : ℝ) (K : ℕ) : Mixed 2 :=
  (dyadicMidpointLaw K).map (complementaryPairPoint B)

theorem complementaryPairDyadicLaw_CDF_error (B : ℝ) (K : ℕ) :
    CDFClose (complementaryPairDyadicLaw B K) (complementaryPairLaw B) (1 / (2 * (2 : ℝ) ^ K)) := by
  intro j z
  change |(Measure.map (fun x : Allocation 2 => x j)
      (Measure.map (complementaryPairPoint B) (dyadicMidpointLaw K : Measure ℝ))).real _ -
    (Measure.map (fun x : Allocation 2 => x j)
      (Measure.map (complementaryPairPoint B) (unitUniform : Measure ℝ))).real _| ≤ _
  rw [Measure.map_map (measurable_pi_apply j) (measurable_complementaryPairPoint B),
    Measure.map_map (measurable_pi_apply j) (measurable_complementaryPairPoint B)]
  fin_cases j
  · have he : (fun x : Allocation 2 => x 0) ∘ complementaryPairPoint B = affineLine 0 B := by
      funext t; dsimp [Function.comp_def, complementaryPairPoint, affineLine]; ring
    change |(Measure.map ((fun x : Allocation 2 => x 0) ∘ complementaryPairPoint B) (dyadicMidpointLaw K : Measure ℝ)).real _ -
      (Measure.map ((fun x : Allocation 2 => x 0) ∘ complementaryPairPoint B) (unitUniform : Measure ℝ)).real _| ≤ _
    rw [he]
    exact (dyadicMidpointLaw_CDF_error K).affine 0 B z
  · have he : (fun x : Allocation 2 => x 1) ∘ complementaryPairPoint B = affineLine B 0 := by
      funext t; dsimp [Function.comp_def, complementaryPairPoint, affineLine]; ring
    change |(Measure.map ((fun x : Allocation 2 => x 1) ∘ complementaryPairPoint B) (dyadicMidpointLaw K : Measure ℝ)).real _ -
      (Measure.map ((fun x : Allocation 2 => x 1) ∘ complementaryPairPoint B) (unitUniform : Measure ℝ)).real _| ≤ _
    rw [he]
    exact (dyadicMidpointLaw_CDF_error K).affine B 0 z

theorem complementaryPairDyadicLaw_fullBudget {B : ℝ} (hB : 0 ≤ B) (K : ℕ) :
    ∀ᵐ x ∂(complementaryPairDyadicLaw B K : Measure (Allocation 2)), FullBudget B x := by
  have hm : ∀ᵐ t ∂(dyadicMidpointLaw K : Measure ℝ), 0 ≤ t ∧ t ≤ 1 := by
    rw [dyadicMidpointLaw_eq]
    exact midpointLaw_supported _
  change ∀ᵐ x ∂Measure.map (complementaryPairPoint B) (dyadicMidpointLaw K : Measure ℝ), FullBudget B x
  rw [ae_map_iff (measurable_complementaryPairPoint B).aemeasurable (measurable_fullBudget B)]
  exact hm.mono (fun _ ht => complementaryPairPoint_fullBudget hB ht)

namespace UniformGroupSpec

noncomputable def dyadicLaw {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) : Mixed m := by
  by_cases h2 : m = 2
  · subst m; exact complementaryPairDyadicLaw i.B K
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.threeInput.dyadicLaw K

theorem dyadicLaw_CDF_error {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) :
    CDFClose (i.dyadicLaw hm K) (i.law hm) (3 / (2 * (2 : ℝ) ^ K)) := by
  have he : 1 / (2 * (2 : ℝ) ^ K) ≤ 3 / (2 * (2 : ℝ) ^ K) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  rcases hm with rfl | rfl
  · change CDFClose (complementaryPairDyadicLaw i.B K) (complementaryPairLaw i.B) _
    exact (complementaryPairDyadicLaw_CDF_error i.B K).mono he
  · change CDFClose (i.threeInput.dyadicLaw K) i.threeInput.law _
    exact (i.threeInput.dyadicLaw_CDF_error K).mono he

theorem dyadicLaw_fullBudget {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw hm K : Measure (Allocation m)), FullBudget i.B x := by
  rcases hm with rfl | rfl
  · change ∀ᵐ x ∂(complementaryPairDyadicLaw i.B K : Measure (Allocation 2)), FullBudget i.B x
    exact complementaryPairDyadicLaw_fullBudget (le_of_lt i.B_pos) K
  · change ∀ᵐ x ∂(i.threeInput.dyadicLaw K : Measure (Allocation 3)), FullBudget i.B x
    exact i.threeInput.dyadicLaw_fullBudget K

end UniformGroupSpec

namespace MixedGroupSpec

noncomputable def dyadicLaw {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) : Mixed (m + 1) := by
  by_cases h2 : m = 2
  · subst m; exact i.threeInput.dyadicLaw K
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.fourInput.dyadicLaw K

theorem dyadicLaw_CDF_error {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) :
    CDFClose (i.dyadicLaw hm K) (i.law hm) (3 / (2 * (2 : ℝ) ^ K)) := by
  rcases hm with rfl | rfl
  · change CDFClose (i.threeInput.dyadicLaw K) i.threeInput.law _
    exact (i.threeInput.dyadicLaw_CDF_error K).mono
      (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (by positivity))
  · change CDFClose (i.fourInput.dyadicLaw K) i.fourInput.law _
    exact i.fourInput.dyadicLaw_CDF_error K

theorem dyadicLaw_fullBudget {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw hm K : Measure (Allocation (m + 1))), FullBudget i.B x := by
  rcases hm with rfl | rfl
  · change ∀ᵐ x ∂(i.threeInput.dyadicLaw K : Measure (Allocation 3)), FullBudget i.B x
    exact i.threeInput.dyadicLaw_fullBudget K
  · change ∀ᵐ x ∂(i.fourInput.dyadicLaw K : Measure (Allocation 4)), FullBudget i.B x
    exact i.fourInput.dyadicLaw_fullBudget K

end MixedGroupSpec
end Blotto
