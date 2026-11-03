import Blotto.RationalWholeRowKernel
import Blotto.ProductSecurityHistoryLaws
import Blotto.RawImplicitSecurityState
import Blotto.UniformNatRejection

/-! The actual temporal Gibbs whole law is the uniform mixture of the
history's proper suffix laws. The newest observation is excluded at each
suffix, matching the trainer's pre-update average exactly. Duplicate code rows
and their joint weights are preserved. -/

namespace Blotto.ProductSecurityTrainer
open scoped BigOperators Classical

def temporalSuffix {m : ℕ} (past : List (RawObservation m)) (time : Fin past.length) :
    List (RawObservation m) := past.drop (time.val + 1)

theorem temporalSuffix_length {m : ℕ} (past : List (RawObservation m)) (time : Fin past.length) :
    (temporalSuffix past time).length ≤ past.length := by
  simp only [temporalSuffix, List.length_drop]
  omega

theorem rawHistoryVectorSum_suffix {m r : ℕ}
    (weights : List (RawObservation m) → Fin r → ℝ) (past : List (RawObservation m)) (i : Fin r) :
    rawHistoryVectorSum weights past i = ∑ time : Fin past.length, weights (temporalSuffix past time) i := by
  induction past with
  | nil => simp [rawHistoryVectorSum]
  | cons x past ih =>
    simp only [rawHistoryVectorSum]
    rw [ih]
    simp only [List.length_cons, Fin.sum_univ_succ, temporalSuffix, Fin.val_zero,
      List.drop_succ_cons, List.drop_zero, Fin.val_succ]
    ring

theorem rawPreparedA_rowKernel {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (past : List (RawObservation (n + 1))) (test : (Fin (n + 1) → ℚ) → ℝ) :
    (c.rawPreparedA past).rationalTargetKernel.mean test = (c.rawLawA past).rowKernel.mean test := by
  unfold rawPreparedA
  rw [ProductArrayTree.prepareSampler_rational_target_mean]
  rfl

theorem temporal_rowKernel_suffix_mean {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length)
    (test : (Fin (n + 1) → ℚ) → ℝ) :
    (c.averageLawA past hPast).rowKernel.mean test =
      (UniformNatRejection.targetKernel past.length hPast).mean
        (fun time => (c.rawPreparedA (temporalSuffix past time)).rationalTargetKernel.mean test) := by
  simp_rw [rawPreparedA_rowKernel]
  change (∑ i, (c.averageLawA past hPast).realWeight i * test ((c.averageLawA past hPast).row i)) = _
  simp only [averageLawA_realWeight, averageLawA_rows, RationalWholeRowLaw.rowKernel,
    UniformNatRejection.targetKernel]
  unfold rawHistoryAverage
  simp_rw [rawHistoryVectorSum_suffix]
  simp only [div_eq_mul_inv]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro time _
  apply Finset.sum_congr rfl
  intro i _
  have hRow : (c.rawLawA (temporalSuffix past time)).row i =
      fun j => c.bidsA j (c.codeA i j) := rfl
  rw [hRow]
  ring

end Blotto.ProductSecurityTrainer
