import Blotto.NestedResourceSystem
import Blotto.Complementary

/-! Reflect a three-coordinate law inside its own box, and append a zero
fourth coordinate. This transformation preserves feasibility on every path. -/

namespace Blotto
open MeasureTheory Set Filter
open scoped BigOperators

noncomputable def reflectAppend (L : Allocation 3) (y : Allocation 3) : Allocation 4 :=
  ![L 0 - y 0, L 1 - y 1, L 2 - y 2, 0]

theorem measurable_reflectAppend (L : Allocation 3) : Measurable (reflectAppend L) := by
  apply Measurable.of_eval
  intro j
  fin_cases j <;> simp [reflectAppend] <;> fun_prop

theorem reflectAppend_fullBudget {B M : ℝ} {L y : Allocation 3}
    (hL : ∑ j, L j = B + M) (hy : FullBudget M y) (hb : InBox L y) :
    FullBudget B (reflectAppend L y) := by
  constructor
  · intro j
    fin_cases j
    · exact sub_nonneg.mpr (hb 0).2
    · exact sub_nonneg.mpr (hb 1).2
    · exact sub_nonneg.mpr (hb 2).2
    · exact le_rfl
  · have hs := hy.2
    simp [Fin.sum_univ_succ] at hL hs
    simp [reflectAppend, Fin.sum_univ_succ]
    linarith

noncomputable def reflectedLaw (L : Allocation 3) (μ : Mixed 3) : Mixed 4 := μ.map (reflectAppend L)

theorem reflectedLaw_fullBudget {B M : ℝ} (L : Allocation 3) (μ : Mixed 3)
    (hL : ∑ j, L j = B + M)
    (hμ : ∀ᵐ y ∂(μ : Measure (Allocation 3)), FullBudget M y)
    (hbox : ∀ᵐ y ∂(μ : Measure (Allocation 3)), InBox L y) :
    ∀ᵐ x ∂(reflectedLaw L μ : Measure (Allocation 4)), FullBudget B x := by
  change ∀ᵐ x ∂Measure.map (reflectAppend L) (μ : Measure (Allocation 3)), FullBudget B x
  rw [ae_map_iff (measurable_reflectAppend L).aemeasurable (measurable_fullBudget B)]
  exact (hμ.and hbox).mono fun _ h => reflectAppend_fullBudget hL h.1 h.2

theorem reflect_affineUniform (L a b : ℝ) :
    Measure.map (fun y => L - y) (affineUniform a b : Measure ℝ) =
      (affineUniform (L - a) (L - b) : Measure ℝ) := by
  change Measure.map (fun y => L - y) (Measure.map (affineLine a b) (unitUniform : Measure ℝ)) =
    Measure.map (affineLine (L - a) (L - b)) (unitUniform : Measure ℝ)
  rw [Measure.map_map (g := fun y : ℝ => L - y) (measurable_const.sub measurable_id)
    (measurable_affineLine a b)]
  congr 1
  funext t
  dsimp [Function.comp_def, affineLine]
  ring

theorem reflect_uniformLaw {T L : ℝ} (hT : 0 < T) :
    Measure.map (fun y => L - y) (uniformLaw T) = (affineUniform (L - T) L : Measure ℝ) := by
  rw [← affineUniform_zero_uniformLaw hT, reflect_affineUniform, sub_zero,
    affineUniform_reverse L (L - T)]

theorem reflectedLaw_marginal_first (L : Allocation 3) (μ : Mixed 3) (j : Fin 3) :
    (marginal (reflectedLaw L μ) j.castSucc : Measure ℝ) =
      Measure.map (fun y => L j - y) (marginal μ j : Measure ℝ) := by
  change Measure.map (fun x : Allocation 4 => x j.castSucc)
    (Measure.map (reflectAppend L) (μ : Measure (Allocation 3))) =
      Measure.map (fun y => L j - y) (Measure.map (fun y : Allocation 3 => y j) (μ : Measure (Allocation 3)))
  rw [Measure.map_map (measurable_pi_apply j.castSucc) (measurable_reflectAppend L),
    Measure.map_map (g := fun y : ℝ => L j - y) (measurable_const.sub measurable_id) (measurable_pi_apply j)]
  congr 1
  funext y
  fin_cases j <;> rfl

theorem reflectedLaw_marginal_last (L : Allocation 3) (μ : Mixed 3) :
    (marginal (reflectedLaw L μ) 3 : Measure ℝ) = Measure.dirac 0 := by
  change Measure.map (fun x : Allocation 4 => x 3)
    (Measure.map (reflectAppend L) (μ : Measure (Allocation 3))) = _
  rw [Measure.map_map (measurable_pi_apply 3) (measurable_reflectAppend L)]
  have he : (fun x : Allocation 4 => x 3) ∘ reflectAppend L = fun _ : Allocation 3 => (0 : ℝ) := rfl
  rw [he, Measure.map_const, measure_univ, one_smul]

end Blotto
