import Blotto.FiniteRejectionExecution

/-! Each proposal record is paired with its exact importance acceptance coin.
The resulting actual first-success runner has the certified target output mass.
Coin implementation, full proposal construction and bit costs remain separate. -/

namespace Blotto
open scoped BigOperators Classical
namespace FiniteImportanceProposal

noncomputable def attempt {r n : ℕ} (q : FiniteImportanceProposal r n) (bound : ℝ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) : FiniteRejectionAttempt (r * 2) n where
  probability := fun i =>
    let p := (finProdFinEquiv.symm i).1
    let flag := (finProdFinEquiv.symm i).2
    q.probability p * (if flag = 0 then q.importance p / bound else 1 - q.importance p / bound)
  result := fun i =>
    if (finProdFinEquiv.symm i).2 = 0 then some (q.output (finProdFinEquiv.symm i).1) else none
  nonnegative := by
    intro i
    apply mul_nonneg (q.probability_nonnegative _)
    split_ifs
    · exact le_of_lt (q.importance_coin_valid hb h _).1
    · have he := (q.importance_coin_valid hb h (finProdFinEquiv.symm i).1).2
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

theorem attempt_outputMass {r n : ℕ} (q : FiniteImportanceProposal r n) (bound : ℝ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (x : Fin n) :
    (q.attempt bound hb h).outputMass x = q.acceptedOutputWeight bound x := by
  unfold FiniteRejectionAttempt.outputMass attempt acceptedOutputWeight acceptedWeight
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Fin.sum_univ_two]
  norm_num

theorem attempt_failureMass {r n : ℕ} (q : FiniteImportanceProposal r n) (bound : ℝ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) :
    (q.attempt bound hb h).failureMass = 1 - q.acceptanceMass bound := by
  unfold FiniteRejectionAttempt.failureMass attempt
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  have he : ∀ p : Fin r, (∑ flag : Fin 2,
      if (if flag = 0 then some (q.output p) else none) = none then
        q.probability p * (if flag = 0 then q.importance p / bound else 1 - q.importance p / bound) else 0) =
          q.probability p - q.acceptedWeight bound p := by
    intro p
    simp only [Fin.sum_univ_two]
    norm_num [acceptedWeight]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, q.probability_sum]
  rfl

theorem attempt_acceptanceMass {r n : ℕ} (q : FiniteImportanceProposal r n) (bound : ℝ)
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) :
    (q.attempt bound hb h).acceptanceMass = q.acceptanceMass bound := by
  unfold FiniteRejectionAttempt.acceptanceMass
  rw [q.attempt_failureMass]
  ring

theorem run_output_target {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (hm : 0 < q.targetMass)
    (k : ℕ) (x : Fin n) :
    (q.attempt bound hb h).pathMean k
      (fun path => if (q.attempt bound hb h).run k path = some x then 1 else 0) =
        (1 - rejectionFailure (q.acceptanceMass bound) k) * (q.targetWeight x / q.targetMass) := by
  rw [FiniteRejectionAttempt.run_output_mean, q.attempt_acceptanceMass, q.attempt_outputMass]
  exact q.boundedOutputWeight_eq hb hm k x

theorem run_failure_target {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (k : ℕ) :
    (q.attempt bound hb h).pathMean k
      (fun path => if (q.attempt bound hb h).run k path = none then 1 else 0) =
        rejectionFailure (q.acceptanceMass bound) k := by
  rw [FiniteRejectionAttempt.run_failure_mean, q.attempt_failureMass]
  rfl

end FiniteImportanceProposal
end Blotto
