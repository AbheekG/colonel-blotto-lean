import Blotto.GeneralPaperCodeCDF

/-! One normalized signed block, with all positive thresholds followed by
all negative thresholds. Its exact pairing with a row CDF is the signed
tail at that row's code. Signs are not separately normalized.
-/
namespace Blotto.GeneralPaperSignedPairing
open scoped BigOperators Classical
open GeneralPaperCodeCDF
set_option autoImplicit false
set_option maxHeartbeats 3500000

def project {n : ℕ} (s : Fin (n+n)) : Fin n :=
  if hs : s.val<n then ⟨s.val,hs⟩ else ⟨s.val-n,by have := s.isLt; omega⟩

def signed {n : ℕ} (delta : Fin n → ℝ) (s : Fin (n+n)) : ℝ :=
  if s.val<n then delta (project s) else -delta (project s)

def pair {n : ℕ} (lambda : Fin (n+n) → ℝ) (delta : Fin n → ℝ) : ℝ := ∑ s, lambda s*signed delta s

def tail {n : ℕ} (lambda : Fin (n+n) → ℝ) (a : ℕ) : ℝ :=
  (prefixSum lambda n-prefixSum lambda a)-(prefixSum lambda (n+n)-prefixSum lambda (n+a))

def rowCDF {n : ℕ} (row : Fin n) (a : Fin n) : ℝ := if row.val≤a.val then 1 else 0

theorem project_positive {n : ℕ} (a : Fin n) : project (Fin.castAdd n a)=a := by
  apply Fin.ext
  simp only [project,Fin.val_castAdd,a.isLt,dite_true]

theorem project_negative {n : ℕ} (a : Fin n) : project (Fin.natAdd n a)=a := by
  apply Fin.ext
  simp only [project,Fin.val_natAdd,show ¬n+a.val<n by omega,dite_false,Nat.add_sub_cancel_left]

theorem signed_positive {n : ℕ} (delta : Fin n → ℝ) (a : Fin n) : signed delta (Fin.castAdd n a)=delta a := by
  simp only [signed,Fin.val_castAdd,a.isLt,ite_true,project_positive]

theorem signed_negative {n : ℕ} (delta : Fin n → ℝ) (a : Fin n) : signed delta (Fin.natAdd n a)= -delta a := by
  simp only [signed,Fin.val_natAdd,show ¬n+a.val<n by omega,ite_false,project_negative]

theorem pair_split {n : ℕ} (lambda : Fin (n+n) → ℝ) (delta : Fin n → ℝ) :
    pair lambda delta=∑ a, (lambda (Fin.castAdd n a)-lambda (Fin.natAdd n a))*delta a := by
  unfold pair
  rw [Fin.sum_univ_add,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [signed_positive,signed_negative]
  ring

theorem signed_sub {n : ℕ} (delta other : Fin n → ℝ) (s : Fin (n+n)) :
    signed (fun i => delta i-other i) s=signed delta s-signed other s := by
  unfold signed
  split_ifs <;> ring

theorem pair_sub_left {n : ℕ} (lambda other : Fin (n+n) → ℝ) (delta : Fin n → ℝ) :
    pair (fun s => lambda s-other s) delta=pair lambda delta-pair other delta := by
  simp only [pair,sub_mul,Finset.sum_sub_distrib]

theorem pair_sub_right {n : ℕ} (lambda : Fin (n+n) → ℝ) (delta other : Fin n → ℝ) :
    pair lambda (fun a => delta a-other a)=pair lambda delta-pair lambda other := by
  simp only [pair,signed_sub,mul_sub,Finset.sum_sub_distrib]

theorem pair_neg {n : ℕ} (lambda : Fin (n+n) → ℝ) (delta : Fin n → ℝ) :
    pair lambda (fun a => -delta a)= -pair lambda delta := by
  unfold pair signed
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs <;> ring

theorem pair_row {n : ℕ} (lambda : Fin (n+n) → ℝ) (row : Fin n) :
    pair lambda (rowCDF row)=tail lambda row.val := by
  unfold pair tail prefixSum
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  unfold signed rowCDF project
  by_cases hp : s.val<n
  · simp only [hp,ite_true,dite_true]
    have hn : s.val<n+n := s.isLt
    have hlast : s.val<n+row.val := by omega
    simp only [hn,hlast,ite_true]
    split_ifs <;> first | omega | ring
  · simp only [hp,ite_false,dite_false]
    have hn : s.val<n+n := s.isLt
    have hnot : ¬s.val<row.val := by have := row.isLt; omega
    simp only [hn,hnot,ite_true,ite_false]
    split_ifs <;> first | omega | ring

theorem cdf_pair_tail {n : ℕ} (lambda : Fin (n+n) → ℝ) (p : Fin n → ℝ) :
    pair lambda (cdf p)=∑ a, p a*tail lambda a.val := by
  rw [pair_split]
  unfold cdf prefixSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← pair_row lambda a,pair_split]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  unfold rowCDF
  split_ifs <;> first | omega | ring

end Blotto.GeneralPaperSignedPairing
