import Blotto.AdaptiveChoiceMoment
import Blotto.RealCDFDistance

/-! Exact ideal probabilities of a finite adaptive rational program. The
digit identity decomposes its whole future distribution, not just the next
Boolean outcome, so adaptive continuations are included. -/

namespace Blotto.AdaptiveChoiceTree
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def idealLaw {α : Type*} [MeasurableSpace α] : AdaptiveChoiceTree α → ProbabilityMeasure α
  | .leaf x => ⟨Measure.dirac x, inferInstance⟩
  | .fork p hp upper lower => probabilityMixture ![(p : ℝ), 1 - (p : ℝ)] ![upper.idealLaw, lower.idealLaw]
      (by
        have h : (0 : ℝ) ≤ p ∧ (p : ℝ) ≤ 1 := by exact_mod_cast hp
        intro j
        fin_cases j
        · exact h.1
        · exact sub_nonneg.mpr h.2)
      (by simp [Fin.sum_univ_succ])

noncomputable def mean {α : Type*} (f : α → ℝ) : AdaptiveChoiceTree α → ℝ
  | .leaf x => f x
  | .fork p _ upper lower => (p : ℝ) * upper.mean f + (1 - (p : ℝ)) * lower.mean f

theorem mean_nonnegative {α : Type*} (T : AdaptiveChoiceTree α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ T.mean f := by
  induction T with
  | leaf x => exact hf x
  | fork p hp upper lower hu hl =>
    have h : (0 : ℝ) ≤ p ∧ (p : ℝ) ≤ 1 := by exact_mod_cast hp
    exact add_nonneg (mul_nonneg h.1 hu) (mul_nonneg (sub_nonneg.mpr h.2) hl)

theorem idealLaw_real_event {α : Type*} [MeasurableSpace α] (T : AdaptiveChoiceTree α) (A : Set α) (hA : MeasurableSet A) :
    (T.idealLaw : Measure α).real A = T.mean (fun x => if x ∈ A then (1 : ℝ) else 0) := by
  induction T with
  | leaf x =>
    by_cases hx : x ∈ A <;> simp [idealLaw, mean, Measure.real, Measure.dirac_apply' _ hA, hx]
  | fork p hp upper lower hu hl =>
    rw [idealLaw, probabilityMixture_real_apply _ _ _ _ _ hA]
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Finset.univ_unique, Finset.sum_singleton]
    change (p : ℝ) * (upper.idealLaw : Measure α).real A +
      (1 - (p : ℝ)) * (lower.idealLaw : Measure α).real A = _
    rw [hu, hl]
    rfl

theorem mean_digit_identity {α : Type*} (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (upper lower : AdaptiveChoiceTree α)
    (f : α → ℝ) :
    (AdaptiveChoiceTree.fork p hp upper lower).mean f =
      (1 / 2 : ℝ) * (AdaptiveChoiceTree.fork (coinResidual p) (coinResidual_bounds hp) upper lower).mean f +
      (1 / 2 : ℝ) * (if probabilityDigit p then upper else lower).mean f := by
  cases hd : probabilityDigit p
  · simp only [Bool.false_eq_true, ite_false, mean]
    have he : (coinResidual p : ℝ) = 2 * (p : ℝ) := by simp [coinResidual, hd]
    rw [he]
    ring
  · simp only [ite_true, mean]
    have he : (coinResidual p : ℝ) = 2 * (p : ℝ) - 1 := by simp [coinResidual, hd]
    rw [he]
    ring

end Blotto.AdaptiveChoiceTree
