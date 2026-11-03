import Blotto.RationalFiniteAttempt

/-! Rational proposal/importance arrays compile to record × acceptance labels.
No expanded recursive product is recommended as the compact sampler: this
finite interface is an exact reference and reusable local compilation step. -/

namespace Blotto
open scoped BigOperators Classical

structure RationalImportanceData (records outputs : ℕ) where
  output : Fin records → Fin outputs
  probability : Fin records → ℚ
  importance : Fin records → ℚ
  probability_nonnegative : ∀ p, 0 ≤ probability p
  probability_sum : ∑ p, probability p = 1
  importance_nonnegative : ∀ p, 0 ≤ importance p

namespace RationalImportanceData

def attempt {r n : ℕ} (q : RationalImportanceData r n) (bound : ℚ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (fallback : Fin r) : RationalFiniteAttempt (r * 2) n where
  weight := fun i =>
    let p := (finProdFinEquiv.symm i).1
    let flag := (finProdFinEquiv.symm i).2
    q.probability p * (if flag = 0 then q.importance p / bound else 1 - q.importance p / bound)
  nonnegative := by
    intro i
    apply mul_nonneg (q.probability_nonnegative _)
    split_ifs
    · exact div_nonneg (q.importance_nonnegative _) hb.le
    · have he := (div_le_one hb).mpr (h (finProdFinEquiv.symm i).1)
      linarith
  sum_one := by
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type]
    have he : ∀ p : Fin r, (∑ flag : Fin 2, q.probability p *
        (if flag = 0 then q.importance p / bound else 1 - q.importance p / bound)) = q.probability p := by
      intro p
      simp only [Fin.sum_univ_two]
      norm_num
      ring
    simp_rw [he]
    exact q.probability_sum
  decode := fun i => if (finProdFinEquiv.symm i).2 = 0 then
    some (q.output (finProdFinEquiv.symm i).1) else none
  fallbackLabel := finProdFinEquiv (fallback, 1)

theorem fallback_decode_none {r n : ℕ} (q : RationalImportanceData r n) (bound : ℚ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (fallback : Fin r) :
    (q.attempt bound hb h fallback).decode (q.attempt bound hb h fallback).fallbackLabel = none := by
  change (if (finProdFinEquiv.symm (finProdFinEquiv (fallback, (1 : Fin 2)))).2 = 0 then
    some (q.output (finProdFinEquiv.symm (finProdFinEquiv (fallback, (1 : Fin 2)))).1) else none) = none
  rw [Equiv.symm_apply_apply]
  norm_num

theorem attempt_success_output {r n : ℕ} (q : RationalImportanceData r n) (bound : ℚ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (fallback : Fin r)
    (i : Fin (r * 2)) (x : Fin n) (hx : (q.attempt bound hb h fallback).decode i = some x) :
    ∃ p, q.output p = x := by
  unfold attempt at hx
  dsimp only at hx
  split at hx
  · exact ⟨_, Option.some.inj hx⟩
  · cases hx

theorem bitpath_success_output {r n : ℕ} (q : RationalImportanceData r n) (bound : ℚ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (fallback : Fin r)
    (K : ℕ) (bits : Fin ((q.attempt bound hb h fallback).bitBudget K) → Bool) (x : Fin n)
    (hx : (q.attempt bound hb h fallback).sample K bits = some x) :
    ∃ p, q.output p = x :=
  q.attempt_success_output bound hb h fallback _ x hx

theorem attempt_real_refines {r n : ℕ} (q : RationalImportanceData r n)
    (cert : FiniteImportanceProposal r n)
    (hOutput : q.output = cert.output)
    (hProbability : ∀ p, (q.probability p : ℝ) = cert.probability p)
    (hImportance : ∀ p, (q.importance p : ℝ) = cert.importance p)
    (bound : ℚ) (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (fallback : Fin r)
    (hc : ∀ p, cert.importance p ≤ (bound : ℝ)) :
    (q.attempt bound hb h fallback).realAttempt =
      cert.attempt (bound : ℝ) (by exact_mod_cast hb) hc := by
  have hP : (q.attempt bound hb h fallback).realAttempt.probability =
      (cert.attempt (bound : ℝ) (by exact_mod_cast hb) hc).probability := by
    funext i
    simp only [attempt, RationalFiniteAttempt.realAttempt, FiniteImportanceProposal.attempt]
    split_ifs <;> simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_one, hProbability, hImportance]
  have hR : (q.attempt bound hb h fallback).realAttempt.result =
      (cert.attempt (bound : ℝ) (by exact_mod_cast hb) hc).result := by
    funext i
    simp only [attempt, RationalFiniteAttempt.realAttempt, FiniteImportanceProposal.attempt, hOutput]
  cases ha : (q.attempt bound hb h fallback).realAttempt
  cases hc' : cert.attempt (bound : ℝ) (by exact_mod_cast hb) hc
  simp only [ha, hc'] at hP hR
  cases hP
  cases hR
  rfl

theorem bitpath_feasible {r n : ℕ} (q : RationalImportanceData r n) (predicate : Fin n → Prop)
    (hFeasible : ∀ p, predicate (q.output p)) (bound : ℚ) (hb : 0 < bound)
    (h : ∀ p, q.importance p ≤ bound) (fallbackRecord : Fin r) (fallbackOutput : Fin n)
    (hf : predicate fallbackOutput) (K : ℕ)
    (bits : Fin ((q.attempt bound hb h fallbackRecord).bitBudget K) → Bool) :
    predicate (((q.attempt bound hb h fallbackRecord).sample K bits).getD fallbackOutput) := by
  cases he : (q.attempt bound hb h fallbackRecord).sample K bits with
  | none => exact hf
  | some x =>
      rcases q.bitpath_success_output bound hb h fallbackRecord K bits x he with ⟨p, hp⟩
      exact hp ▸ hFeasible p

theorem bitBudget_bound {r n : ℕ} (q : RationalImportanceData r n) (bound : ℚ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (fallback : Fin r) (K : ℕ) :
    (q.attempt bound hb h fallback).bitBudget K ≤ 3 * (2 * r + K) := by
  have he := (q.attempt bound hb h fallback).bitBudget_bound K
  simpa only [Nat.mul_comm r 2] using he

end RationalImportanceData
end Blotto
