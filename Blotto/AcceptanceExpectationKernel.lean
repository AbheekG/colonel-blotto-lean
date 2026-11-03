import Blotto.RationalFiniteKernel

/-! Acceptance is a Markov kernel on proposal outcomes, including explicit
proposal failure. Exact acceptance postprocessing contracts source error; its
own bounded rational coin contributes one additional primitive allowance. -/

namespace Blotto
open scoped BigOperators Classical

noncomputable def bernoulliOutputKernel {α : Type*} (probability : ℝ)
    (hp : 0 ≤ probability ∧ probability ≤ 1) (accepted rejected : α) : BoundedExpectationKernel α where
  mean := fun f => probability * f accepted + (1 - probability) * f rejected
  constant := by intro c; ring
  monotone := by
    intro f g h
    exact add_le_add (mul_le_mul_of_nonneg_left (h accepted) hp.1)
      (mul_le_mul_of_nonneg_left (h rejected) (sub_nonneg.mpr hp.2))
  add := by intro f g; ring

noncomputable def acceptanceKernel {α : Type*} (probability : α → ℝ)
    (hp : ∀ x, 0 ≤ probability x ∧ probability x ≤ 1) : Option α → BoundedExpectationKernel (Option α)
  | none => BoundedExpectationKernel.point none
  | some x => bernoulliOutputKernel (probability x) (hp x) (some x) none

theorem acceptance_contraction {α : Type*} (actual ideal : BoundedExpectationKernel (Option α))
    (probability : α → ℝ) (hp : ∀ x, 0 ≤ probability x ∧ probability x ≤ 1)
    (error : ℝ) (h : actual.Close ideal error) :
    (actual.bind (acceptanceKernel probability hp)).Close
      (ideal.bind (acceptanceKernel probability hp)) error := by
  intro f hf
  exact h (fun x => (acceptanceKernel probability hp x).mean f)
    (fun x => (acceptanceKernel probability hp x).mean_unit f hf)

theorem acceptance_coin_perturbation {α : Type*} (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1)
    (error : ℝ) (hn : 0 ≤ error) (h : ∀ x, |p x - q x| ≤ error) (value : Option α) :
    (acceptanceKernel p hp value).Close (acceptanceKernel q hq value) error := by
  intro f hf
  cases value with
  | none => simp only [acceptanceKernel, sub_self, abs_zero]; exact hn
  | some x =>
    change |(p x * f (some x) + (1 - p x) * f none) -
      (q x * f (some x) + (1 - q x) * f none)| ≤ error
    have he : (p x * f (some x) + (1 - p x) * f none) -
      (q x * f (some x) + (1 - q x) * f none) = (p x - q x) * (f (some x) - f none) := by ring
    rw [he, abs_mul]
    have hfabs : |f (some x) - f none| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hf (some x)).1,(hf (some x)).2,(hf none).1,(hf none).2]
    calc
      _ ≤ error * 1 := mul_le_mul (h x) hfabs (abs_nonneg _) hn
      _ = error := mul_one _

end Blotto
