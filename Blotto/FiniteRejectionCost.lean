import Blotto.FiniteRejectionEvents

/-! The actual first-success loop inspects at most its supplied cap. Product
attempt means give the truncated geometric expected count, so uniform charged
attempt work has explicit expected and worst-case bounds. -/

namespace Blotto
open scoped BigOperators Classical

def firstAcceptedVisits {α : Type*} : List (Option α) → ℕ
  | [] => 0
  | none :: rest => 1 + firstAcceptedVisits rest
  | some _ :: _ => 1

theorem firstAcceptedVisits_le_length {α : Type*} (items : List (Option α)) :
    firstAcceptedVisits items ≤ items.length := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases item with
    | none => simpa only [firstAcceptedVisits, List.length_cons, Nat.add_comm] using Nat.add_le_add_left ih 1
    | some x => simp [firstAcceptedVisits]

namespace FiniteRejectionAttempt

def visits {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ) (path : Fin k → Fin r) : ℕ :=
  firstAcceptedVisits (List.ofFn (fun j => a.result (path j)))

theorem visits_le_cap {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ) (path : Fin k → Fin r) :
    a.visits k path ≤ k := by
  simpa only [visits, List.length_ofFn] using
    firstAcceptedVisits_le_length (List.ofFn (fun j => a.result (path j)))

theorem visits_cons {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ)
    (i : Fin r) (path : Fin k → Fin r) :
    a.visits (k + 1) (Fin.cons i path) =
      1 + if a.result i = none then a.visits k path else 0 := by
  unfold visits
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  cases a.result i <;> simp [firstAcceptedVisits]

theorem pathMean_smul {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ)
    (c : ℝ) (f : (Fin k → Fin r) → ℝ) :
    a.pathMean k (fun path => c * f path) = c * a.pathMean k f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pathMean, ih]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem visits_mean {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ) :
    a.pathMean k (fun path => (a.visits k path : ℝ)) = rejectionExpectedAttempts a.acceptanceMass k := by
  induction k with
  | zero => simp [pathMean, visits, firstAcceptedVisits, rejectionExpectedAttempts]
  | succ k ih =>
    rw [pathMean, rejectionExpectedAttempts]
    have he : ∀ i : Fin r, a.pathMean k (fun tail => (a.visits (k + 1) (Fin.cons i tail) : ℝ)) =
        1 + if a.result i = none then rejectionExpectedAttempts a.acceptanceMass k else 0 := by
      intro i
      simp_rw [a.visits_cons, Nat.cast_add, Nat.cast_one]
      rw [a.pathMean_add, a.pathMean_constant]
      by_cases h : a.result i = none
      · simp only [h, ite_true, ih]
      · simp only [h, ite_false, Nat.cast_zero, a.pathMean_constant]
    simp_rw [he, mul_add, mul_one]
    rw [Finset.sum_add_distrib, a.sum_one]
    congr 1
    have ht : (∑ i, a.probability i * (if a.result i = none then
        rejectionExpectedAttempts a.acceptanceMass k else 0)) =
          a.failureMass * rejectionExpectedAttempts a.acceptanceMass k := by
      unfold failureMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [ht]
    unfold acceptanceMass
    ring

theorem uniformWork_le_cap {r n : ℕ} (a : FiniteRejectionAttempt r n) (k work : ℕ)
    (path : Fin k → Fin r) : work * a.visits k path ≤ work * k :=
  Nat.mul_le_mul_left work (a.visits_le_cap k path)

end FiniteRejectionAttempt
namespace FiniteImportanceProposal

theorem run_visits_mean_le_factor {r n : ℕ} (q : FiniteImportanceProposal r n) {z factor : ℝ}
    (hz : 0 < z) (hg : 1 ≤ factor) (hLower : z ≤ q.targetMass)
    (hImportance : ∀ p, q.importance p ≤ z * factor) (k : ℕ) :
    (q.attempt (z * factor) (mul_pos hz (by linarith)) hImportance).pathMean k
      (fun path => ((q.attempt (z * factor) (mul_pos hz (by linarith)) hImportance).visits k path : ℝ)) ≤ factor := by
  rw [FiniteRejectionAttempt.visits_mean, q.attempt_acceptanceMass]
  exact q.boundedExpectedAttempts_le_factor hz hg hLower hImportance k

end FiniteImportanceProposal
end Blotto
