import Blotto.GeneralPaperFourAverageGap

/-! Finite probability mixtures of complete code rows. Real probabilities
are allowed for proof comparators. Marginals retain the original joint row
index and are used only as linear observers in the source analysis.
-/
namespace Blotto.GeneralPaperCodeMixture
open scoped BigOperators
open GeneralPaperCodeCDF GeneralPaperSignedPairing GeneralPaperFourLossAlgebra GeneralPaperCodeAverages
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Mixture (m n : ℕ) where
  labels : ℕ
  weight : Fin labels → ℝ
  rows : Fin labels → Fin m → Fin n
  nonnegative : ∀ l, 0≤weight l
  total : ∑ l, weight l=1

def marginal {m n : ℕ} (law : Mixture m n) (j : Fin m) (i : Fin n) : ℝ :=
  ∑ l, law.weight l*point (law.rows l j) i

theorem marginal_probability {m n : ℕ} (law : Mixture m n) (j : Fin m) : Probability (marginal law j) := by
  constructor
  · intro i
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (law.nonnegative l) ((point_probability (law.rows l j)).1 i))
  · unfold marginal
    rw [Finset.sum_comm]
    calc
      _ = ∑ l, law.weight l*(∑ i, point (law.rows l j) i) := by simp only [Finset.mul_sum]
      _ = ∑ l, law.weight l := by simp only [(point_probability _).2,mul_one]
      _ = 1 := law.total

theorem marginal_dot {m n : ℕ} (law : Mixture m n) (j : Fin m) (f : Fin n → ℝ) :
    dot (marginal law j) f=∑ l, law.weight l*dot (point (law.rows l j)) f := by
  unfold dot marginal
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem point_dot {n : ℕ} (row : Fin n) (f : Fin n → ℝ) : dot (point row) f=f row := by
  simp only [dot,point,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem marginal_cdf {m n : ℕ} (law : Mixture m n) (j : Fin m) (a : Fin n) :
    cdf (marginal law j) a=∑ l, law.weight l*rowCDF (law.rows l j) a := by
  unfold cdf
  rw [prefix_dot,marginal_dot]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← prefix_dot]
  exact congrArg (fun value => law.weight l*value) (point_cdf (law.rows l j) a)

theorem marginal_pair {m n : ℕ} (law : Mixture m n) (j : Fin m) (lambda : Fin (n+n) → ℝ) :
    pair lambda (cdf (marginal law j))=∑ l, law.weight l*tail lambda (law.rows l j).val := by
  rw [cdf_pair_tail]
  change dot (marginal law j) (fun i => tail lambda i.val)=_
  rw [marginal_dot]
  simp only [point_dot]

theorem residual_split {m n : ℕ} (law : Mixture m n) (j : Fin m) (lambda : Fin (n+n) → ℝ) (row : Fin n) :
    tail lambda row.val-pair lambda (cdf (marginal law j))=
      ∑ l, law.weight l*(tail lambda row.val-tail lambda (law.rows l j).val) := by
  rw [marginal_pair]
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,law.total,one_mul]

theorem weighted_residual {m n : ℕ} (law : Mixture m n) (v : Fin m → ℝ)
    (lambda : Fin m → Fin (n+n) → ℝ) (row : Fin m → Fin n) :
    (∑ j, v j*(tail (lambda j) (row j).val-pair (lambda j) (cdf (marginal law j))))=
      ∑ l, law.weight l*(∑ j, v j*(tail (lambda j) (row j).val-tail (lambda j) (law.rows l j).val)) := by
  simp only [residual_split,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Blotto.GeneralPaperCodeMixture
