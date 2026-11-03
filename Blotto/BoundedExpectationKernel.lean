import Blotto.RationalFiniteAttemptMean

/-! Probability-kernel expectations contract uniform test errors. This small
interface supports dependent sequential composition, keeping hypotheses about
each actual/ideal kernel explicit rather than asserting independence for free. -/

namespace Blotto

structure BoundedExpectationKernel (α : Type*) where
  mean : (α → ℝ) → ℝ
  constant : ∀ c, mean (fun _ => c) = c
  monotone : ∀ f g, (∀ x, f x ≤ g x) → mean f ≤ mean g
  add : ∀ f g, mean (fun x => f x + g x) = mean f + mean g

namespace BoundedExpectationKernel

theorem mean_unit {α : Type*} (k : BoundedExpectationKernel α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : 0 ≤ k.mean f ∧ k.mean f ≤ 1 := by
  have h0 := k.monotone (fun _ => 0) f (fun x => (hf x).1)
  have h1 := k.monotone f (fun _ => 1) (fun x => (hf x).2)
  rw [k.constant] at h0 h1
  exact ⟨h0, h1⟩

theorem contraction {α : Type*} (k : BoundedExpectationKernel α) (f g : α → ℝ)
    (error : ℝ) (h : ∀ x, |f x - g x| ≤ error) : |k.mean f - k.mean g| ≤ error := by
  have hlo := k.monotone (fun x => g x + -error) f (fun x => by have he := (abs_le.mp (h x)).1; linarith)
  have hhi := k.monotone f (fun x => g x + error) (fun x => by have he := (abs_le.mp (h x)).2; linarith)
  rw [k.add, k.constant] at hlo hhi
  rw [abs_le]
  constructor <;> linarith

noncomputable def bind {α β : Type*} (k : BoundedExpectationKernel α)
    (next : α → BoundedExpectationKernel β) : BoundedExpectationKernel β where
  mean := fun f => k.mean (fun x => (next x).mean f)
  constant := by intro c; simp only [(next _).constant, k.constant]
  monotone := by
    intro f g h
    apply k.monotone
    intro x
    exact (next x).monotone f g h
  add := by
    intro f g
    simp only [(next _).add, k.add]

def Close {α : Type*} (a b : BoundedExpectationKernel α) (error : ℝ) : Prop :=
  ∀ f : α → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) → |a.mean f - b.mean f| ≤ error

theorem bind_close {α β : Type*} (a b : BoundedExpectationKernel α)
    (nextA nextB : α → BoundedExpectationKernel β) (sourceError continuationError : ℝ)
    (hSource : a.Close b sourceError) (hNext : ∀ x, (nextA x).Close (nextB x) continuationError) :
    (a.bind nextA).Close (b.bind nextB) (sourceError + continuationError) := by
  intro f hf
  have hContinuation := a.contraction (fun x => (nextA x).mean f) (fun x => (nextB x).mean f)
    continuationError (fun x => hNext x f hf)
  have hSource' := hSource (fun x => (nextB x).mean f) (fun x => (nextB x).mean_unit f hf)
  have hTriangle := abs_sub_le (a.mean (fun x => (nextA x).mean f))
    (a.mean (fun x => (nextB x).mean f)) (b.mean (fun x => (nextB x).mean f))
  change |a.mean (fun x => (nextA x).mean f) - b.mean (fun x => (nextB x).mean f)| ≤ _
  linarith

end BoundedExpectationKernel
end Blotto
