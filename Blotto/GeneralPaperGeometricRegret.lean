import Blotto.GeneralPaperGeometricLevels

/-! Deterministic regret for the selected exact integer-level trajectory.
The exponential update is proved from those levels, not assumed as an input.
The local executed-loss bound and approximation error are explicit interfaces
to the compressed CDF-query implementation; neither is a convergence oracle.
-/
namespace Blotto.GeneralPaperGeometricRegret
open scoped BigOperators Classical
open SparseMW GeneralPaperGeometricLevels
set_option autoImplicit false

def cumulative {n : ℕ} (p loss : ℕ → Fin n → ℝ) (u : Fin n → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ i, (p t i-u i)*loss t i

theorem rate_bounds (eta theta : ℚ) (hEta : 0 < eta) (hTheta : 0 < theta)
    (hProduct : eta*theta ≤ 1) :
    (eta : ℝ) ≤ rate (geometricBase eta theta) theta ∧
      rate (geometricBase eta theta) theta ≤ 2*(eta : ℝ) := by
  have hbQ := base_bounds eta theta hEta hTheta hProduct
  let b : ℝ := geometricBase eta theta
  have hb : 1/2 ≤ b := by
    have hh : (1:ℚ) ≤ 2*geometricBase eta theta := by linarith [hbQ.1]
    have hc : (1:ℝ) ≤ 2*(geometricBase eta theta:ℝ) := by exact_mod_cast hh
    change (1:ℝ)/2 ≤ (geometricBase eta theta:ℝ)
    linarith
  have hbPos : 0 < b := by linarith
  have hbOne : b < 1 := by change (geometricBase eta theta:ℝ) < 1; exact_mod_cast hbQ.2
  have ht : (0 : ℝ) < theta := by exact_mod_cast hTheta
  have hbEq : b = 1-(eta : ℝ)*(theta : ℝ)/2 := by simp [b, geometricBase]
  have hLogUpper := Real.log_le_sub_one_of_pos hbPos
  have hLogNeg := (Real.log_neg hbPos hbOne).le
  have hLogLower := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hbPos) hbPos.le
  have hInv := mul_inv_cancel₀ (ne_of_gt hbPos)
  have hAux := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ b-1/2) hLogNeg
  change (eta : ℝ) ≤ -2*Real.log b/(theta : ℝ) ∧
    -2*Real.log b/(theta : ℝ) ≤ 2*(eta : ℝ)
  constructor
  · apply (le_div_iff₀ ht).mpr
    nlinarith
  · apply (div_le_iff₀ ht).mpr
    nlinarith

theorem executed_regret {n : ℕ} (hn : 0 < n) (base theta : ℚ)
    (hBase : 0 < base) (hOne : base < 1) (hTheta : 0 < theta)
    (increment : ℕ → Fin n → ℕ) (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hsu : ∑ i, u i = 1)
    (cap : ℝ) (hCap : ∀ t i, |(executedLoss theta (increment t i) : ℝ)| ≤ cap) (T : ℕ) :
    cumulative (probability base increment) (fun t i => (executedLoss theta (increment t i) : ℝ)) u T ≤
      Real.log n / rate base theta + rate base theta * T * cap^2 / 2 := by
  have hk := rate_positive base theta hBase hOne hTheta
  have he := finite_uniform_signed_sharp_regret hn u (probability base increment)
    (fun t i => (executedLoss theta (increment t i) : ℝ)) (rate base theta) (fun _ => cap)
    hu hsu (probability_positive hn base hBase increment) (probability_sum hn base hBase increment)
    (initial_uniform base increment) hk.le hCap (probability_step hn base theta hBase hOne hTheta increment) T
  have hSum : (∑ _t ∈ Finset.range T, cap^2) = (T : ℝ)*cap^2 := by simp
  rw [hSum] at he
  apply (mul_le_mul_iff_left₀ hk).mp
  dsimp only [cumulative] at *
  calc
    _ ≤ Real.log n + (rate base theta ^ 2/2)*((T : ℝ)*cap^2) := by nlinarith only [he]
    _ = (Real.log n / rate base theta + rate base theta * T * cap^2 / 2)*rate base theta := by
      field_simp
      <;> ring

theorem pairing_perturbation {n : ℕ} (p u truth executed : Fin n → ℝ) (error : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsp : ∑ i, p i = 1)
    (hu : ∀ i, 0 ≤ u i) (hsu : ∑ i, u i = 1)
    (hError : ∀ i, |truth i-executed i| ≤ error) :
    (∑ i, (p i-u i)*truth i) ≤ (∑ i, (p i-u i)*executed i)+2*error := by
  calc
    _ ≤ ∑ i, ((p i-u i)*executed i + (p i+u i)*error) := by
      apply Finset.sum_le_sum
      intro i _
      have he := abs_le.mp (hError i)
      have h1 := mul_le_mul_of_nonneg_left he.2 (hp i)
      have h2 := mul_le_mul_of_nonneg_left (show executed i-truth i ≤ error by linarith) (hu i)
      nlinarith
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_add_distrib, hsp, hsu]
      ring

theorem cumulative_perturbation {n : ℕ} (p truth executed : ℕ → Fin n → ℝ)
    (u : Fin n → ℝ) (error : ℝ)
    (hp : ∀ t i, 0 ≤ p t i) (hsp : ∀ t, ∑ i, p t i = 1)
    (hu : ∀ i, 0 ≤ u i) (hsu : ∑ i, u i = 1)
    (hError : ∀ t i, |truth t i-executed t i| ≤ error) (T : ℕ) :
    cumulative p truth u T ≤ cumulative p executed u T+2*T*error := by
  have h := Finset.sum_le_sum (s := Finset.range T) (fun t _ =>
    pairing_perturbation (p t) u (truth t) (executed t) error (hp t) (hsp t) hu hsu (hError t))
  simpa [cumulative, Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_comm] using h

theorem true_regret {n : ℕ} (hn : 0 < n) (base theta : ℚ)
    (hBase : 0 < base) (hOne : base < 1) (hTheta : 0 < theta)
    (increment : ℕ → Fin n → ℕ) (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hsu : ∑ i, u i = 1)
    (truth : ℕ → Fin n → ℝ) (cap error : ℝ)
    (hCap : ∀ t i, |(executedLoss theta (increment t i) : ℝ)| ≤ cap)
    (hError : ∀ t i, |truth t i-(executedLoss theta (increment t i) : ℝ)| ≤ error) (T : ℕ) :
    cumulative (probability base increment) truth u T ≤
      Real.log n / rate base theta + rate base theta * T * cap^2 / 2 + 2*T*error := by
  have he := executed_regret hn base theta hBase hOne hTheta increment u hu hsu cap hCap T
  have hp := cumulative_perturbation (probability base increment) truth
    (fun t i => (executedLoss theta (increment t i) : ℝ)) u error
    (fun t i => (probability_positive hn base hBase increment t i).le)
    (probability_sum hn base hBase increment) hu hsu hError T
  linarith

theorem alphabet_log_bound (n lambda : ℕ) (hn : 0 < n) (hSize : n ≤ 2^(lambda+1)) :
    Real.log n ≤ (lambda : ℝ)+1 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (n : ℝ) ≤ (2 : ℝ)^(lambda+1) := by exact_mod_cast hSize
  have he := Real.log_le_log hp hs
  rw [Real.log_pow] at he
  have hl : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hm := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ (lambda+1 : ℕ) by positivity)
  push_cast at he hm
  linarith

end Blotto.GeneralPaperGeometricRegret
