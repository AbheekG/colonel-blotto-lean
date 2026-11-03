import Blotto.UnorderedThree
import Blotto.Complementary

/-! Proportional splitting of a merged pair in a four-uniform coupling.
The caller supplies a pair whose total length is at most the budget. -/

namespace Blotto
open MeasureTheory Set

noncomputable def splitFirstTwo (a d : ℝ) (x : Allocation 3) : Allocation 4 :=
  ![a / (a + d) * x 0, d / (a + d) * x 0, x 1, x 2]

theorem measurable_splitFirstTwo (a d : ℝ) : Measurable (splitFirstTwo a d) := by
  apply Measurable.of_eval
  intro j
  fin_cases j <;> simp [splitFirstTwo] <;> fun_prop

theorem splitFirstTwo_fullBudget {B a d : ℝ} (ha : 0 < a) (hd : 0 < d) {x : Allocation 3}
    (hx : FullBudget B x) : FullBudget B (splitFirstTwo a d x) := by
  have hsum : 0 < a + d := add_pos ha hd
  have hcoef : a / (a + d) + d / (a + d) = 1 := by field_simp [ne_of_gt hsum]
  constructor
  · intro j
    fin_cases j
    · exact mul_nonneg (div_nonneg (le_of_lt ha) (le_of_lt hsum)) (hx.1 0)
    · exact mul_nonneg (div_nonneg (le_of_lt hd) (le_of_lt hsum)) (hx.1 0)
    · exact hx.1 1
    · exact hx.1 2
  · have he := hx.2
    simp [Fin.sum_univ_succ] at he
    simp [splitFirstTwo, Fin.sum_univ_succ]
    nlinarith [congrArg (fun y : ℝ => y * x 0) hcoef]

noncomputable def splitLaw (a d : ℝ) (μ : Mixed 3) : Mixed 4 := μ.map (splitFirstTwo a d)

theorem splitLaw_fullBudget {B a d : ℝ} (ha : 0 < a) (hd : 0 < d) (μ : Mixed 3)
    (hμ : ∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget B x) :
    ∀ᵐ x ∂(splitLaw a d μ : Measure (Allocation 4)), FullBudget B x := by
  change ∀ᵐ x ∂Measure.map (splitFirstTwo a d) (μ : Measure (Allocation 3)), FullBudget B x
  rw [ae_map_iff (measurable_splitFirstTwo a d).aemeasurable (measurable_fullBudget B)]
  exact hμ.mono fun _ hx => splitFirstTwo_fullBudget ha hd hx

theorem scale_affineUniform (k a b : ℝ) :
    Measure.map (fun x => k * x) (affineUniform a b : Measure ℝ) =
      (affineUniform (k * a) (k * b) : Measure ℝ) := by
  change Measure.map (fun x => k * x) (Measure.map (affineLine a b) (unitUniform : Measure ℝ)) =
    Measure.map (affineLine (k * a) (k * b)) (unitUniform : Measure ℝ)
  rw [Measure.map_map (g := fun x : ℝ => k * x) (measurable_const.mul measurable_id)
    (measurable_affineLine a b)]
  congr 1
  funext t
  dsimp [Function.comp_def, affineLine]
  ring

theorem scale_uniformLaw {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Measure.map (fun x => (a / b) * x) (uniformLaw b) = uniformLaw a := by
  rw [← affineUniform_zero_uniformLaw hb, scale_affineUniform, mul_zero,
    div_mul_cancel₀ _ (ne_of_gt hb), affineUniform_zero_uniformLaw ha]

theorem splitLaw_marginals (a d : ℝ) (μ : Mixed 3) :
    (marginal (splitLaw a d μ) 0 : Measure ℝ) =
      Measure.map (fun x => a / (a + d) * x) (marginal μ 0 : Measure ℝ) ∧
    (marginal (splitLaw a d μ) 1 : Measure ℝ) =
      Measure.map (fun x => d / (a + d) * x) (marginal μ 0 : Measure ℝ) ∧
    (marginal (splitLaw a d μ) 2 : Measure ℝ) = (marginal μ 1 : Measure ℝ) ∧
    (marginal (splitLaw a d μ) 3 : Measure ℝ) = (marginal μ 2 : Measure ℝ) := by
  have he : ∀ j : Fin 4, (marginal (splitLaw a d μ) j : Measure ℝ) =
      Measure.map (fun x : Allocation 3 => splitFirstTwo a d x j) (μ : Measure (Allocation 3)) := by
    intro j
    change Measure.map (fun x : Allocation 4 => x j)
      (Measure.map (splitFirstTwo a d) (μ : Measure (Allocation 3))) = _
    rw [Measure.map_map (measurable_pi_apply j) (measurable_splitFirstTwo a d)]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    change Measure.map (fun x : Allocation 3 => a / (a + d) * x 0) _ =
      Measure.map (fun x => a / (a + d) * x) (Measure.map (fun x : Allocation 3 => x 0) _)
    rw [Measure.map_map (g := fun x : ℝ => a / (a + d) * x)
      (measurable_const.mul measurable_id) (measurable_pi_apply 0)]
    rfl
  · rw [he]
    change Measure.map (fun x : Allocation 3 => d / (a + d) * x 0) _ =
      Measure.map (fun x => d / (a + d) * x) (Measure.map (fun x : Allocation 3 => x 0) _)
    rw [Measure.map_map (g := fun x : ℝ => d / (a + d) * x)
      (measurable_const.mul measurable_id) (measurable_pi_apply 0)]
    rfl
  · rw [he]
    rfl
  · rw [he]
    rfl

structure MergeFourInput where
  B : ℝ
  l0 : ℝ
  l1 : ℝ
  l2 : ℝ
  l3 : ℝ
  l0_pos : 0 < l0
  l1_pos : 0 < l1
  l2_pos : 0 < l2
  l3_pos : 0 < l3
  pair_le : l0 + l1 ≤ B
  l2_le : l2 ≤ B
  l3_le : l3 ≤ B
  balance : l0 + l1 + l2 + l3 = 2 * B

namespace MergeFourInput

noncomputable def childSpec (i : MergeFourInput) : ThreeSpec where
  B := i.B
  a := i.l0 + i.l1
  d := i.l2
  c := i.l3
  p := 1
  B_pos := lt_of_lt_of_le i.l2_pos i.l2_le
  a_pos := add_pos i.l0_pos i.l1_pos
  d_pos := i.l2_pos
  c_pos := i.l3_pos
  p_pos := by norm_num
  a_le := i.pair_le
  d_le := i.l2_le
  c_le := i.l3_le
  p_le := le_rfl
  balance := by simpa using i.balance

noncomputable def law (i : MergeFourInput) : Mixed 4 := splitLaw i.l0 i.l1 i.childSpec.law

noncomputable def point (i : MergeFourInput) (edge : Fin 9) (t : ℝ) : Allocation 4 :=
  splitFirstTwo i.l0 i.l1 (i.childSpec.point edge t)

theorem point_fullBudget (i : MergeFourInput) (edge : Fin 9) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    FullBudget i.B (i.point edge t) :=
  splitFirstTwo_fullBudget i.l0_pos i.l1_pos (i.childSpec.point_fullBudget edge ht)

theorem coupling_contract (i : MergeFourInput) :
    (∀ᵐ x ∂(i.law : Measure (Allocation 4)), FullBudget i.B x) ∧
    (marginal i.law 0 : Measure ℝ) = uniformLaw i.l0 ∧
    (marginal i.law 1 : Measure ℝ) = uniformLaw i.l1 ∧
    (marginal i.law 2 : Measure ℝ) = uniformLaw i.l2 ∧
    (marginal i.law 3 : Measure ℝ) = uniformLaw i.l3 := by
  unfold law
  have hc := i.childSpec.law_contract
  have hm := splitLaw_marginals i.l0 i.l1 i.childSpec.law
  refine ⟨splitLaw_fullBudget i.l0_pos i.l1_pos _ hc.1, ?_, ?_, ?_, ?_⟩
  · rw [hm.1, hc.2.1]
    exact scale_uniformLaw i.l0_pos (add_pos i.l0_pos i.l1_pos)
  · rw [hm.2.1, hc.2.1]
    exact scale_uniformLaw i.l1_pos (add_pos i.l0_pos i.l1_pos)
  · exact hm.2.2.1.trans hc.2.2.1
  · rw [hm.2.2.2, hc.2.2.2]
    simp [childSpec, zeroUniformLaw]

end MergeFourInput
end Blotto
