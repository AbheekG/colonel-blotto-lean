import Blotto.FourSpec

/-! Explicit grouped-coordinate laws for two or three uniform groups,
optionally followed by one remaining zero/uniform mixture. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

noncomputable def complementaryPairPoint (B t : ℝ) : Allocation 2 := ![B * t, B * (1 - t)]

theorem measurable_complementaryPairPoint (B : ℝ) : Measurable (complementaryPairPoint B) := by
  apply Measurable.of_eval
  intro j
  fin_cases j <;> simp [complementaryPairPoint] <;> fun_prop

theorem complementaryPairPoint_fullBudget {B t : ℝ} (hB : 0 ≤ B) (ht : 0 ≤ t ∧ t ≤ 1) :
    FullBudget B (complementaryPairPoint B t) := by
  constructor
  · intro j
    fin_cases j
    · exact mul_nonneg hB ht.1
    · exact mul_nonneg hB (sub_nonneg.mpr ht.2)
  · simp [complementaryPairPoint, Fin.sum_univ_succ]
    ring

noncomputable def complementaryPairLaw (B : ℝ) : Mixed 2 := unitUniform.map (complementaryPairPoint B)

theorem complementaryPairLaw_contract {B : ℝ} (hB : 0 < B) :
    (∀ᵐ x ∂(complementaryPairLaw B : Measure (Allocation 2)), FullBudget B x) ∧
      ∀ j, (marginal (complementaryPairLaw B) j : Measure ℝ) = uniformLaw B := by
  constructor
  · change ∀ᵐ x ∂Measure.map (complementaryPairPoint B) (unitUniform : Measure ℝ), FullBudget B x
    rw [ae_map_iff (measurable_complementaryPairPoint B).aemeasurable (measurable_fullBudget B)]
    exact unitUniform_supported.mono fun _ ht => complementaryPairPoint_fullBudget (le_of_lt hB) ht
  · intro j
    change Measure.map (fun x : Allocation 2 => x j)
      (Measure.map (complementaryPairPoint B) (unitUniform : Measure ℝ)) = _
    rw [Measure.map_map (measurable_pi_apply j) (measurable_complementaryPairPoint B)]
    fin_cases j
    · have he : (fun x : Allocation 2 => x 0) ∘ complementaryPairPoint B = affineLine 0 B := by
        funext t; dsimp [Function.comp_def, complementaryPairPoint, affineLine]; ring
      change Measure.map ((fun x : Allocation 2 => x 0) ∘ complementaryPairPoint B) (unitUniform : Measure ℝ) = _
      rw [he]
      exact affineUniform_zero_uniformLaw hB
    · have he : (fun x : Allocation 2 => x 1) ∘ complementaryPairPoint B = affineLine B 0 := by
        funext t; dsimp [Function.comp_def, complementaryPairPoint, affineLine]; ring
      change Measure.map ((fun x : Allocation 2 => x 1) ∘ complementaryPairPoint B) (unitUniform : Measure ℝ) = _
      rw [he]
      change (affineUniform B 0 : Measure ℝ) = _
      rw [affineUniform_reverse B 0, affineUniform_zero_uniformLaw hB]

structure UniformGroupSpec (m : ℕ) where
  B : ℝ
  length : Allocation m
  B_pos : 0 < B
  length_pos : ∀ j, 0 < length j
  length_le : ∀ j, length j ≤ B
  balance : (∑ j, length j) = 2 * B

namespace UniformGroupSpec

noncomputable def threeInput (i : UniformGroupSpec 3) : ThreeSpec where
  B := i.B
  a := i.length 0
  d := i.length 1
  c := i.length 2
  p := 1
  B_pos := i.B_pos
  a_pos := i.length_pos 0
  d_pos := i.length_pos 1
  c_pos := i.length_pos 2
  p_pos := by norm_num
  a_le := i.length_le 0
  d_le := i.length_le 1
  c_le := i.length_le 2
  p_le := le_rfl
  balance := by simpa [Fin.sum_univ_succ, add_assoc] using i.balance

theorem pair_lengths (i : UniformGroupSpec 2) : ∀ j, i.length j = i.B := by
  have hs := i.balance
  simp [Fin.sum_univ_succ] at hs
  have h0 := i.length_le 0
  have h1 := i.length_le 1
  intro j
  fin_cases j
  · change i.length 0 = i.B; linarith
  · change i.length 1 = i.B; linarith

noncomputable def law {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3) : Mixed m := by
  by_cases h2 : m = 2
  · subst m; exact complementaryPairLaw i.B
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.threeInput.law

theorem law_contract {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3) :
    (∀ᵐ x ∂(i.law hm : Measure (Allocation m)), FullBudget i.B x) ∧
      ∀ j, (marginal (i.law hm) j : Measure ℝ) = uniformLaw (i.length j) := by
  rcases hm with rfl | rfl
  · change (∀ᵐ x ∂(complementaryPairLaw i.B : Measure (Allocation 2)), FullBudget i.B x) ∧
      ∀ j, (marginal (complementaryPairLaw i.B) j : Measure ℝ) = uniformLaw (i.length j)
    have hc := complementaryPairLaw_contract i.B_pos
    refine ⟨hc.1, ?_⟩
    intro j
    rw [i.pair_lengths j]
    exact hc.2 j
  · change (∀ᵐ x ∂(i.threeInput.law : Measure (Allocation 3)), FullBudget i.B x) ∧
      ∀ j, (marginal i.threeInput.law j : Measure ℝ) = uniformLaw (i.length j)
    have hc := i.threeInput.law_contract
    refine ⟨hc.1, ?_⟩
    intro j
    fin_cases j
    · exact hc.2.1
    · exact hc.2.2.1
    · simpa [threeInput, zeroUniformLaw] using hc.2.2.2

end UniformGroupSpec

structure MixedGroupSpec (m : ℕ) where
  B : ℝ
  length : Allocation m
  ell : ℝ
  p : ℝ
  B_pos : 0 < B
  length_pos : ∀ j, 0 < length j
  length_le : ∀ j, length j ≤ B
  ell_pos : 0 < ell
  ell_le : ell ≤ B
  p_pos : 0 < p
  p_lt : p < 1
  balance : (∑ j, length j) + p * ell = 2 * B

namespace MixedGroupSpec

noncomputable def threeInput (i : MixedGroupSpec 2) : ThreeSpec where
  B := i.B
  a := i.length 0
  d := i.length 1
  c := i.ell
  p := i.p
  B_pos := i.B_pos
  a_pos := i.length_pos 0
  d_pos := i.length_pos 1
  c_pos := i.ell_pos
  p_pos := i.p_pos
  a_le := i.length_le 0
  d_le := i.length_le 1
  c_le := i.ell_le
  p_le := le_of_lt i.p_lt
  balance := by simpa [Fin.sum_univ_succ, add_assoc] using i.balance

noncomputable def fourInput (i : MixedGroupSpec 3) : FourSpec :=
  ⟨i.B, i.length, i.ell, i.p, i.length_pos, i.length_le, i.ell_pos, i.ell_le, i.p_pos, i.p_lt, i.balance⟩

noncomputable def law {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3) : Mixed (m + 1) := by
  by_cases h2 : m = 2
  · subst m; exact i.threeInput.law
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.fourInput.law

theorem law_contract {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3) :
    (∀ᵐ x ∂(i.law hm : Measure (Allocation (m + 1))), FullBudget i.B x) ∧
      (∀ j, (marginal (i.law hm) j.castSucc : Measure ℝ) = uniformLaw (i.length j)) ∧
      (marginal (i.law hm) (Fin.last m) : Measure ℝ) = zeroUniformLaw i.ell i.p := by
  rcases hm with rfl | rfl
  · change (∀ᵐ x ∂(i.threeInput.law : Measure (Allocation 3)), FullBudget i.B x) ∧
      (∀ j, (marginal i.threeInput.law j.castSucc : Measure ℝ) = uniformLaw (i.length j)) ∧
      (marginal i.threeInput.law (Fin.last 2) : Measure ℝ) = zeroUniformLaw i.ell i.p
    have hc := i.threeInput.law_contract
    refine ⟨hc.1, ?_, hc.2.2.2⟩
    intro j
    fin_cases j
    · exact hc.2.1
    · exact hc.2.2.1
  · change (∀ᵐ x ∂(i.fourInput.law : Measure (Allocation 4)), FullBudget i.B x) ∧
      (∀ j, (marginal i.fourInput.law j.castSucc : Measure ℝ) = uniformLaw (i.length j)) ∧
      (marginal i.fourInput.law (Fin.last 3) : Measure ℝ) = zeroUniformLaw i.ell i.p
    exact i.fourInput.law_contract

end MixedGroupSpec
end Blotto
