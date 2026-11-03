import Blotto.FiniteRejectionAttempts

/-! An actual first-success list runner refines finite product-attempt means.
Each attempt has its own independent index; the theorem does not equate arbitrary
correlated attempt laws with this product semantics. -/

namespace Blotto
open scoped BigOperators Classical

def firstAccepted {α : Type*} : List (Option α) → Option α
  | [] => none
  | none :: rest => firstAccepted rest
  | some x :: _ => some x

structure FiniteRejectionAttempt (attempts outputs : ℕ) where
  probability : Fin attempts → ℝ
  result : Fin attempts → Option (Fin outputs)
  nonnegative : ∀ i, 0 ≤ probability i
  sum_one : ∑ i, probability i = 1

namespace FiniteRejectionAttempt

noncomputable def failureMass {r n : ℕ} (a : FiniteRejectionAttempt r n) : ℝ :=
  ∑ i, if a.result i = none then a.probability i else 0

noncomputable def outputMass {r n : ℕ} (a : FiniteRejectionAttempt r n) (x : Fin n) : ℝ :=
  ∑ i, if a.result i = some x then a.probability i else 0

noncomputable def acceptanceMass {r n : ℕ} (a : FiniteRejectionAttempt r n) : ℝ := 1 - a.failureMass

noncomputable def pathMean {r n : ℕ} (a : FiniteRejectionAttempt r n) :
    (k : ℕ) → ((Fin k → Fin r) → ℝ) → ℝ
  | 0, f => f Fin.elim0
  | k + 1, f => ∑ i, a.probability i *
      a.pathMean k (fun tail => f (Fin.cons i tail))

def run {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ) (path : Fin k → Fin r) : Option (Fin n) :=
  firstAccepted (List.ofFn (fun j => a.result (path j)))

theorem pathMean_constant {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ) (value : ℝ) :
    a.pathMean k (fun _ => value) = value := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pathMean, ih]
    rw [← Finset.sum_mul, a.sum_one, one_mul]

theorem run_cons {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ)
    (i : Fin r) (path : Fin k → Fin r) :
    a.run (k + 1) (Fin.cons i path) =
      match a.result i with
      | none => a.run k path
      | some x => some x := by
  unfold run
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  cases a.result i <;> rfl

theorem failureMass_unit {r n : ℕ} (a : FiniteRejectionAttempt r n) :
    0 ≤ a.failureMass ∧ a.failureMass ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact a.nonnegative i
    · rfl
  · calc
      a.failureMass ≤ ∑ i, a.probability i := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · exact le_rfl
        · exact a.nonnegative i
      _ = 1 := a.sum_one

theorem acceptanceMass_unit {r n : ℕ} (a : FiniteRejectionAttempt r n) :
    0 ≤ a.acceptanceMass ∧ a.acceptanceMass ≤ 1 := by
  have h := a.failureMass_unit
  unfold acceptanceMass
  constructor <;> linarith

theorem run_failure_mean {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ) :
    a.pathMean k (fun path => if a.run k path = none then 1 else 0) = a.failureMass ^ k := by
  induction k with
  | zero => simp [pathMean, run, firstAccepted]
  | succ k ih =>
    rw [pathMean]
    have he : ∀ i, a.pathMean k (fun tail => if a.run (k + 1) (Fin.cons i tail) = none then 1 else 0) =
        if a.result i = none then a.failureMass ^ k else 0 := by
      intro i
      simp only [a.run_cons]
      cases h : a.result i with
      | none => simpa only [h, ite_true] using ih
      | some x => simp only [Option.some_ne_none, ite_false, a.pathMean_constant]
    simp_rw [he]
    calc
      (∑ i, a.probability i * (if a.result i = none then a.failureMass ^ k else 0)) =
          (∑ i, if a.result i = none then a.probability i else 0) * a.failureMass ^ k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = _ := by unfold failureMass; rw [pow_succ]; ring

theorem run_output_mean {r n : ℕ} (a : FiniteRejectionAttempt r n) (k : ℕ) (x : Fin n) :
    a.pathMean k (fun path => if a.run k path = some x then 1 else 0) =
      rejectionSuccessMass a.acceptanceMass (a.outputMass x) k := by
  induction k with
  | zero => simp [pathMean, run, firstAccepted, rejectionSuccessMass]
  | succ k ih =>
    rw [pathMean, rejectionSuccessMass]
    have he : ∀ i, a.pathMean k (fun tail => if a.run (k + 1) (Fin.cons i tail) = some x then 1 else 0) =
        (if a.result i = some x then 1 else 0) +
          (if a.result i = none then rejectionSuccessMass a.acceptanceMass (a.outputMass x) k else 0) := by
      intro i
      simp only [a.run_cons]
      cases h : a.result i with
      | none => simpa using ih
      | some y => simp [a.pathMean_constant]
    simp_rw [he, mul_add]
    rw [Finset.sum_add_distrib]
    have hFirst : (∑ i, a.probability i * (if a.result i = some x then 1 else 0)) = a.outputMass x := by
      unfold outputMass
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    have hRest : (∑ i, a.probability i * (if a.result i = none then
        rejectionSuccessMass a.acceptanceMass (a.outputMass x) k else 0)) =
          a.failureMass * rejectionSuccessMass a.acceptanceMass (a.outputMass x) k := by
      unfold failureMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [hFirst, hRest]
    unfold acceptanceMass
    ring

end FiniteRejectionAttempt
end Blotto
