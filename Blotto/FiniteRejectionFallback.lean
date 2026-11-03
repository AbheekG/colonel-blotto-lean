import Blotto.FiniteRejectionSupport

/-! A bounded first-success draw followed by one feasible fallback has the
exact target/fallback mixture law. Failure mass controls every singleton error;
the generic scalar event bound is available for event sums as well. -/

namespace Blotto
open scoped BigOperators Classical
namespace FiniteRejectionAttempt

theorem pathMean_add {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ)
    (f g : (Fin k → Fin r) → ℝ) :
    a.pathMean k (fun path => f path + g path) = a.pathMean k f + a.pathMean k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pathMean, ih, mul_add, Finset.sum_add_distrib]

theorem fallback_output_mean {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ)
    (fallback x : Fin n) :
    a.pathMean k (fun path => if (a.run k path).getD fallback = x then 1 else 0) =
      rejectionSuccessMass a.acceptanceMass (a.outputMass x) k +
        (if fallback = x then a.failureMass ^ k else 0) := by
  have he : ∀ path, (if (a.run k path).getD fallback = x then (1 : ℝ) else 0) =
      (if a.run k path = some x then 1 else 0) +
        (if fallback = x then (if a.run k path = none then 1 else 0) else 0) := by
    intro path
    cases h : a.run k path <;> simp
  simp_rw [he]
  rw [a.pathMean_add, a.run_output_mean]
  by_cases hf : fallback = x
  · simp only [hf, ite_true, a.run_failure_mean]
  · simp only [hf, ite_false, a.pathMean_constant, add_zero]

end FiniteRejectionAttempt
namespace FiniteImportanceProposal

theorem targetProbability_unit {r n : ℕ} (q : FiniteImportanceProposal r n)
    (hm : 0 < q.targetMass) (x : Fin n) :
    0 ≤ q.targetWeight x / q.targetMass ∧ q.targetWeight x / q.targetMass ≤ 1 := by
  constructor
  · exact div_nonneg (q.target_nonnegative x) (le_of_lt hm)
  · apply (div_le_one hm).mpr
    exact Finset.single_le_sum (fun i _ => q.target_nonnegative i) (Finset.mem_univ x)

theorem run_fallback_target {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (hm : 0 < q.targetMass)
    (k : ℕ) (fallback x : Fin n) :
    (q.attempt bound hb h).pathMean k
      (fun path => if ((q.attempt bound hb h).run k path).getD fallback = x then 1 else 0) =
        (1 - rejectionFailure (q.acceptanceMass bound) k) * (q.targetWeight x / q.targetMass) +
          rejectionFailure (q.acceptanceMass bound) k * (if fallback = x then 1 else 0) := by
  rw [FiniteRejectionAttempt.fallback_output_mean, q.attempt_acceptanceMass, q.attempt_outputMass,
    q.attempt_failureMass, rejectionSuccessMass_closed (q.acceptanceMass_positive hb hm),
    q.conditionalOutput_eq hb hm]
  unfold rejectionFailure
  split_ifs <;> simp

theorem run_fallback_singleton_error {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (hm : 0 < q.targetMass)
    (k : ℕ) (fallback x : Fin n) :
    |(q.attempt bound hb h).pathMean k
      (fun path => if ((q.attempt bound hb h).run k path).getD fallback = x then 1 else 0) -
        q.targetWeight x / q.targetMass| ≤ rejectionFailure (q.acceptanceMass bound) k := by
  rw [q.run_fallback_target hb h hm]
  have hp := q.acceptanceMass_le_one hb h
  have hn := q.acceptanceMass_positive hb hm
  have hf := (rejectionFailure_unit (le_of_lt hn) hp k).1
  have ht := q.targetProbability_unit hm x
  apply rejectionFallback_event_error hf ht.1 ht.2 <;> split_ifs <;> norm_num

end FiniteImportanceProposal
end Blotto
