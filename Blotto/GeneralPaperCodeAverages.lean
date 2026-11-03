import Blotto.GeneralPaperCatalogueFiniteOptimizer

/-! Exact time averages of finite code laws and complete-row marginals.
CDFs, signed pairings and the half-tie payoff commute with these finite
averages. The empirical law averages whole-row indicators, with one common
row index for every field; it is not a product output law.
-/
namespace Blotto.GeneralPaperCodeAverages
open scoped BigOperators Classical
open GeneralPaperCodeCDF GeneralPaperSignedPairing GeneralPaperFourLossAlgebra
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def mean {α : Type*} (T : ℕ) (sequence : ℕ → α → ℝ) (i : α) : ℝ :=
  (∑ t ∈ Finset.range T, sequence t i)/(T:ℝ)

def point {n : ℕ} (row : Fin n) (i : Fin n) : ℝ := if i=row then 1 else 0

theorem point_probability {n : ℕ} (row : Fin n) : Probability (point row) := by
  constructor
  · intro i
    unfold point
    split_ifs <;> norm_num
  · simp only [point,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem point_cdf {n : ℕ} (row a : Fin n) : cdf (point row) a=rowCDF row a := by
  unfold cdf prefixSum point rowCDF
  have hsum : (∑ i : Fin n, if i.val<a.val+1 then (if i=row then (1:ℝ) else 0) else 0)=
      ∑ i : Fin n, if i=row then (if row.val≤a.val then (1:ℝ) else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases he : i=row
    · subst i
      simp only [ite_true]
      split_ifs <;> first | omega | rfl
    · simp only [he,ite_false,ite_self]
  rw [hsum]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem mean_dot {α : Type*} [Fintype α] (T : ℕ) (sequence : ℕ → α → ℝ) (f : α → ℝ) :
    dot (mean T sequence) f=(∑ t ∈ Finset.range T, dot (sequence t) f)/(T:ℝ) := by
  unfold dot mean
  simp only [div_mul_eq_mul_div,Finset.sum_div,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem prefix_dot {n : ℕ} (p : Fin n → ℝ) (cut : ℕ) :
    prefixSum p cut=dot p (fun i => if i.val<cut then 1 else 0) := by
  unfold prefixSum dot
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  split_ifs <;> ring

theorem prefix_mean {n : ℕ} (T : ℕ) (sequence : ℕ → Fin n → ℝ) (cut : ℕ) :
    prefixSum (mean T sequence) cut=(∑ t ∈ Finset.range T, prefixSum (sequence t) cut)/(T:ℝ) := by
  simp only [prefix_dot]
  exact mean_dot T sequence _

theorem cdf_mean {n : ℕ} (T : ℕ) (sequence : ℕ → Fin n → ℝ) (a : Fin n) :
    cdf (mean T sequence) a=mean T (fun t i => cdf (sequence t) i) a := prefix_mean T sequence _

theorem mean_sub {α : Type*} (T : ℕ) (p q : ℕ → α → ℝ) (i : α) :
    mean T (fun t a => p t a-q t a) i=mean T p i-mean T q i := by
  unfold mean
  rw [Finset.sum_sub_distrib,sub_div]

theorem mean_probability {n : ℕ} (T : ℕ) (hT : 0<T) (sequence : ℕ → Fin n → ℝ)
    (hp : ∀ t<T, Probability (sequence t)) : Probability (mean T sequence) := by
  constructor
  · intro i
    exact div_nonneg (Finset.sum_nonneg (fun t ht => (hp t (Finset.mem_range.mp ht)).1 i)) (Nat.cast_nonneg _)
  · unfold mean
    rw [← Finset.sum_div,Finset.sum_comm]
    have hs : (∑ t ∈ Finset.range T, ∑ i, sequence t i)=(T:ℝ) := by
      calc
        _ = ∑ _t ∈ Finset.range T, (1:ℝ) := Finset.sum_congr rfl (fun t ht => (hp t (Finset.mem_range.mp ht)).2)
        _ = _ := by simp
    rw [hs,div_self (by exact_mod_cast hT.ne')]

theorem pair_dot {n : ℕ} (lambda : Fin (n+n) → ℝ) (delta : Fin n → ℝ) :
    pair lambda delta=dot delta (fun a => lambda (Fin.castAdd n a)-lambda (Fin.natAdd n a)) := by
  rw [pair_split]
  unfold dot
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem pair_mean {n : ℕ} (T : ℕ) (lambda : Fin (n+n) → ℝ) (delta : ℕ → Fin n → ℝ) :
    pair lambda (mean T delta)=(∑ t ∈ Finset.range T, pair lambda (delta t))/(T:ℝ) := by
  simp only [pair_dot]
  exact mean_dot T delta _

theorem payoff_mean_left {n : ℕ} (T : ℕ) (p : ℕ → Fin n → ℝ) (q : Fin n → ℝ) (hq : ∑ i, q i=1) :
    codePayoff (mean T p) q=(∑ t ∈ Finset.range T, codePayoff (p t) q)/(T:ℝ) := by
  simp only [payoff_defender _ q hq]
  exact mean_dot T p _

theorem payoff_mean_right {n : ℕ} (T : ℕ) (p : Fin n → ℝ) (q : ℕ → Fin n → ℝ) :
    codePayoff p (mean T q)=(∑ t ∈ Finset.range T, codePayoff p (q t))/(T:ℝ) := by
  simp only [payoff_response]
  exact mean_dot T q _

noncomputable def empirical {n : ℕ} (T : ℕ) (rows : ℕ → Fin n) : Fin n → ℝ := mean T (fun t => point (rows t))

theorem empirical_probability {n : ℕ} (T : ℕ) (hT : 0<T) (rows : ℕ → Fin n) : Probability (empirical T rows) :=
  mean_probability T hT _ (fun t _ => point_probability (rows t))

theorem empirical_cdf {n : ℕ} (T : ℕ) (rows : ℕ → Fin n) (a : Fin n) :
    cdf (empirical T rows) a=mean T (fun t => rowCDF (rows t)) a := by
  unfold empirical
  rw [cdf_mean]
  unfold mean
  simp only [point_cdf]

theorem cdf_difference_mean {n : ℕ} (T : ℕ) (p : ℕ → Fin n → ℝ) (rows : ℕ → Fin n) (a : Fin n) :
    cdf (mean T p) a-cdf (empirical T rows) a=
      mean T (fun t i => cdf (p t) i-rowCDF (rows t) i) a := by
  rw [cdf_mean,empirical_cdf,mean_sub]

end Blotto.GeneralPaperCodeAverages
