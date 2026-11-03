import Blotto.FiniteRejectionFallback

/-! The target/fallback mixture identity and failure-mass error hold for every
finite output event, including CDF prefix events chosen by a caller's row map. -/

namespace Blotto
open scoped BigOperators Classical
namespace FiniteRejectionAttempt

theorem pathMean_sum {r n m : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ)
    (f : Fin m → (Fin k → Fin r) → ℝ) :
    a.pathMean k (fun path => ∑ x, f x path) = ∑ x, a.pathMean k (f x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pathMean, ih]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]

theorem pathMean_nonnegative {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ)
    (f : (Fin k → Fin r) → ℝ) (h : ∀ path, 0 ≤ f path) : 0 ≤ a.pathMean k f := by
  induction k with
  | zero => exact h _
  | succ k ih =>
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (a.nonnegative i) (ih _ (fun tail => h (Fin.cons i tail)))

end FiniteRejectionAttempt
namespace FiniteImportanceProposal

noncomputable def targetEventProbability {r n : ℕ} (q : FiniteImportanceProposal r n)
    (event : Finset (Fin n)) : ℝ :=
  (∑ x, if x ∈ event then q.targetWeight x else 0) / q.targetMass

theorem targetEventProbability_unit {r n : ℕ} (q : FiniteImportanceProposal r n)
    (hm : 0 < q.targetMass) (event : Finset (Fin n)) :
    0 ≤ q.targetEventProbability event ∧ q.targetEventProbability event ≤ 1 := by
  have hnonneg : 0 ≤ (∑ x, if x ∈ event then q.targetWeight x else 0) := by
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact q.target_nonnegative x
    · rfl
  constructor
  · exact div_nonneg hnonneg (le_of_lt hm)
  · apply (div_le_one hm).mpr
    apply Finset.sum_le_sum
    intro x _
    split_ifs
    · exact le_rfl
    · exact q.target_nonnegative x

theorem run_fallback_event {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (hm : 0 < q.targetMass)
    (k : ℕ) (fallback : Fin n) (event : Finset (Fin n)) :
    (q.attempt bound hb h).pathMean k
      (fun path => if ((q.attempt bound hb h).run k path).getD fallback ∈ event then 1 else 0) =
        (1 - rejectionFailure (q.acceptanceMass bound) k) * q.targetEventProbability event +
          rejectionFailure (q.acceptanceMass bound) k * (if fallback ∈ event then 1 else 0) := by
  have he : ∀ y : Fin n, (if y ∈ event then (1 : ℝ) else 0) =
      ∑ x : Fin n, if x ∈ event then (if y = x then 1 else 0) else 0 := by
    intro y
    simp
  simp_rw [he]
  rw [FiniteRejectionAttempt.pathMean_sum]
  have hterm : ∀ x : Fin n,
      (q.attempt bound hb h).pathMean k (fun path => if x ∈ event then
        (if ((q.attempt bound hb h).run k path).getD fallback = x then 1 else 0) else 0) =
          if x ∈ event then
            (1 - rejectionFailure (q.acceptanceMass bound) k) * (q.targetWeight x / q.targetMass) +
              rejectionFailure (q.acceptanceMass bound) k * (if fallback = x then 1 else 0)
          else 0 := by
    intro x
    by_cases hx : x ∈ event
    · simp only [hx, ite_true, q.run_fallback_target hb h hm]
    · simp only [hx, ite_false, FiniteRejectionAttempt.pathMean_constant]
  simp_rw [hterm]
  have hdistribute : ∀ x : Fin n,
      (if x ∈ event then
        (1 - rejectionFailure (q.acceptanceMass bound) k) * (q.targetWeight x / q.targetMass) +
          rejectionFailure (q.acceptanceMass bound) k * (if fallback = x then 1 else 0) else 0) =
        (1 - rejectionFailure (q.acceptanceMass bound) k) *
          ((if x ∈ event then q.targetWeight x else 0) / q.targetMass) +
            rejectionFailure (q.acceptanceMass bound) k *
              (if x ∈ event then (if fallback = x then 1 else 0) else 0) := by
    intro x
    split_ifs <;> simp
  simp_rw [hdistribute]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← he]
  rfl

theorem run_fallback_event_error {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (hm : 0 < q.targetMass)
    (k : ℕ) (fallback : Fin n) (event : Finset (Fin n)) :
    |(q.attempt bound hb h).pathMean k
      (fun path => if ((q.attempt bound hb h).run k path).getD fallback ∈ event then 1 else 0) -
        q.targetEventProbability event| ≤ rejectionFailure (q.acceptanceMass bound) k := by
  rw [q.run_fallback_event hb h hm]
  have hp := q.acceptanceMass_le_one hb h
  have hn := q.acceptanceMass_positive hb hm
  have hf := (rejectionFailure_unit (le_of_lt hn) hp k).1
  have ht := q.targetEventProbability_unit hm event
  apply rejectionFallback_event_error hf ht.1 ht.2 <;> split_ifs <;> norm_num

end FiniteImportanceProposal
end Blotto
