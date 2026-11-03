import Blotto.AcceptanceExpectationKernel

/-! A bounded rational Bernoulli acceptance block realizes the exact acceptance
kernel with 2^-K bounded-test error. Proposal failure bypasses the coin; accepted
record identity is retained, so whole-record feasibility is preserved. -/

namespace Blotto
open scoped BigOperators Classical

def rationalAcceptanceAttempt (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) : RationalFiniteAttempt 2 1 where
  weight := ![p, 1 - p]
  nonnegative := by intro i; fin_cases i; exact hp.1; exact sub_nonneg.mpr hp.2
  sum_one := by simp [Fin.sum_univ_succ]
  decode := fun i => if i = 0 then some 0 else none
  fallbackLabel := 1

noncomputable def rationalAcceptanceKernel {α : Type*} (p : α → ℚ)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (K : ℕ) : Option α → BoundedExpectationKernel (Option α)
  | none => BoundedExpectationKernel.point none
  | some x => (fairBitKernel ((rationalAcceptanceAttempt (p x) (hp x)).bitBudget K)).map
      (fun bits => ((rationalAcceptanceAttempt (p x) (hp x)).sample K bits).map (fun _ => x))

theorem rationalAcceptanceKernel_error {α : Type*} (p : α → ℚ)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (K : ℕ) (value : Option α) :
    (rationalAcceptanceKernel p hp K value).Close
      (acceptanceKernel (fun x => (p x : ℝ)) (fun x => by exact_mod_cast hp x) value) (1 / (2 : ℝ) ^ K) := by
  intro f hf
  cases value with
  | none => simp only [rationalAcceptanceKernel, acceptanceKernel, sub_self, abs_zero]; positivity
  | some x =>
    let a := rationalAcceptanceAttempt (p x) (hp x)
    have he := a.sampleMean_error K (fun result => f (result.map (fun _ => x)))
      (fun result => hf _)
    have hIdeal : a.idealMean (fun result => f (result.map (fun _ => x))) =
        (p x : ℝ) * f (some x) + (1 - (p x : ℝ)) * f none := by
      simp only [RationalFiniteAttempt.idealMean, a, rationalAcceptanceAttempt, Fin.sum_univ_two]
      norm_num
    rw [hIdeal] at he
    exact he

theorem proposal_and_acceptance_error {α : Type*} (actual ideal : BoundedExpectationKernel (Option α))
    (p : α → ℚ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (proposalError : ℝ)
    (h : actual.Close ideal proposalError) (K : ℕ) :
    (actual.bind (rationalAcceptanceKernel p hp K)).Close
      (ideal.bind (acceptanceKernel (fun x => (p x : ℝ)) (fun x => by exact_mod_cast hp x)))
        (proposalError + 1 / (2 : ℝ) ^ K) :=
  BoundedExpectationKernel.bind_close _ _ _ _ _ _ h (rationalAcceptanceKernel_error p hp K)

end Blotto
