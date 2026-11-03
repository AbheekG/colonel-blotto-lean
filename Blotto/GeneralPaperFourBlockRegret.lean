import Blotto.GeneralPaperGeometricRegret

/-! The four selected geometric families, weighted once by the values.
The signed families use their complete signed alphabet as one block. The
local CDF/loss-error hypotheses remain visible and must be discharged by the
compressed query implementation. This is not a whole-game source contract.
-/
namespace Blotto.GeneralPaperFourBlockRegret
open scoped BigOperators Classical
open GeneralPaperGeometricLevels GeneralPaperGeometricRegret
set_option autoImplicit false

def cap (block : Fin 4) : ℝ := if block.val < 2 then 2 else 1

theorem cap_squares : (∑ b : Fin 4, cap b ^ 2) = 10 := by
  norm_num [Fin.sum_univ_succ, cap]

noncomputable def weightedRegret {m n : ℕ} (v : Fin m → ℝ) (base : ℚ)
    (increment : Fin m → ℕ → Fin n → ℕ) (truth : Fin m → ℕ → Fin n → ℝ)
    (u : Fin m → Fin n → ℝ) (T : ℕ) : ℝ :=
  ∑ j, v j * cumulative (probability base (increment j)) (truth j) (u j) T

theorem weighted_regret {m n : ℕ} (hn : 0 < n) (v : Fin m → ℝ)
    (hv : ∀ j, 0 ≤ v j) (hsv : ∑ j, v j = 1) (base theta : ℚ)
    (hBase : 0 < base) (hOne : base < 1) (hTheta : 0 < theta)
    (increment : Fin m → ℕ → Fin n → ℕ) (u : Fin m → Fin n → ℝ)
    (hu : ∀ j i, 0 ≤ u j i) (hsu : ∀ j, ∑ i, u j i = 1)
    (truth : Fin m → ℕ → Fin n → ℝ) (magnitude error : ℝ)
    (hCap : ∀ j t i, |(executedLoss theta (increment j t i) : ℝ)| ≤ magnitude)
    (hError : ∀ j t i, |truth j t i-(executedLoss theta (increment j t i) : ℝ)| ≤ error) (T : ℕ) :
    weightedRegret v base increment truth u T ≤
      Real.log n/rate base theta+rate base theta*T*magnitude^2/2+2*T*error := by
  unfold weightedRegret
  calc
    _ ≤ ∑ j, v j * (Real.log n/rate base theta+rate base theta*T*magnitude^2/2+2*T*error) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (true_regret hn base theta hBase hOne hTheta (increment j) (u j) (hu j) (hsu j)
          (truth j) magnitude error (hCap j) (hError j) T) (hv j)
    _ = _ := by rw [← Finset.sum_mul, hsv, one_mul]

theorem four_regret {m : ℕ} (size : Fin 4 → ℕ) (hSize : ∀ b, 0 < size b)
    (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (hsv : ∑ j, v j = 1) (base theta : ℚ)
    (hBase : 0 < base) (hOne : base < 1) (hTheta : 0 < theta)
    (increment : (b : Fin 4) → Fin m → ℕ → Fin (size b) → ℕ)
    (u : (b : Fin 4) → Fin m → Fin (size b) → ℝ)
    (hu : ∀ b j i, 0 ≤ u b j i) (hsu : ∀ b j, ∑ i, u b j i = 1)
    (truth : (b : Fin 4) → Fin m → ℕ → Fin (size b) → ℝ) (error : ℝ)
    (hCap : ∀ b j t i, |(executedLoss theta (increment b j t i) : ℝ)| ≤ cap b)
    (hError : ∀ b j t i, |truth b j t i-(executedLoss theta (increment b j t i) : ℝ)| ≤ error)
    (T : ℕ) :
    (∑ b, weightedRegret v base (increment b) (truth b) (u b) T) ≤
      (∑ b, Real.log (size b))/rate base theta+5*rate base theta*T+8*T*error := by
  have h := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) =>
    weighted_regret (hSize b) v hv hsv base theta hBase hOne hTheta (increment b) (u b) (hu b) (hsu b)
      (truth b) (cap b) error (hCap b) (hError b) T)
  calc
    _ ≤ ∑ b : Fin 4, (Real.log (size b)/rate base theta+rate base theta*T*cap b^2/2+2*T*error) := h
    _ = _ := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, cap, Fin.val_zero,
        Fin.val_succ, zero_add]
      norm_num
      ring

theorem paper_regret {m : ℕ} (size : Fin 4 → ℕ) (hSize : ∀ b, 0 < size b)
    (lambda : ℕ) (hAlphabet : ∀ b, size b ≤ 2^(lambda+1))
    (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (hsv : ∑ j, v j = 1) (eta theta : ℚ)
    (hEta : 0 < eta) (hTheta : 0 < theta) (hProduct : eta*theta ≤ 1)
    (increment : (b : Fin 4) → Fin m → ℕ → Fin (size b) → ℕ)
    (u : (b : Fin 4) → Fin m → Fin (size b) → ℝ)
    (hu : ∀ b j i, 0 ≤ u b j i) (hsu : ∀ b j, ∑ i, u b j i = 1)
    (truth : (b : Fin 4) → Fin m → ℕ → Fin (size b) → ℝ) (error : ℝ)
    (hCap : ∀ b j t i, |(executedLoss theta (increment b j t i) : ℝ)| ≤ cap b)
    (hError : ∀ b j t i, |truth b j t i-(executedLoss theta (increment b j t i) : ℝ)| ≤ error)
    (T : ℕ) :
    (∑ b, weightedRegret v (geometricBase eta theta) (increment b) (truth b) (u b) T) ≤
      4*((lambda : ℝ)+1)/(eta : ℝ)+20*(eta : ℝ)*T+8*T*error := by
  have hb := base_bounds eta theta hEta hTheta hProduct
  have hbPos : 0 < geometricBase eta theta := by linarith [hb.1]
  have he := four_regret size hSize v hv hsv _ theta hbPos hb.2 hTheta increment u hu hsu truth error hCap hError T
  have hk := rate_bounds eta theta hEta hTheta hProduct
  have hkPos := rate_positive _ theta hbPos hb.2 hTheta
  have hEtaR : (0 : ℝ) < eta := by exact_mod_cast hEta
  have hLogs : (∑ b : Fin 4, Real.log (size b)) ≤ 4*((lambda : ℝ)+1) := by
    calc
      _ ≤ ∑ _b : Fin 4, ((lambda : ℝ)+1) :=
        Finset.sum_le_sum (fun b _ => alphabet_log_bound (size b) lambda (hSize b) (hAlphabet b))
      _ = _ := by simp; ring
  have hDivide := div_le_div_of_nonneg_right hLogs hkPos.le
  have hCompare : 4*((lambda : ℝ)+1)/rate (geometricBase eta theta) theta ≤ 4*((lambda : ℝ)+1)/(eta : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hEtaR hk.1
  have hT : (0 : ℝ) ≤ T := by positivity
  have hRate := mul_le_mul_of_nonneg_right hk.2 hT
  nlinarith

theorem paper_average_regret {m : ℕ} (size : Fin 4 → ℕ) (hSize : ∀ b, 0 < size b)
    (lambda : ℕ) (hAlphabet : ∀ b, size b ≤ 2^(lambda+1))
    (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j) (hsv : ∑ j, v j = 1) (eta theta : ℚ)
    (hEta : 0 < eta) (hTheta : 0 < theta) (hProduct : eta*theta ≤ 1)
    (increment : (b : Fin 4) → Fin m → ℕ → Fin (size b) → ℕ)
    (u : (b : Fin 4) → Fin m → Fin (size b) → ℝ)
    (hu : ∀ b j i, 0 ≤ u b j i) (hsu : ∀ b j, ∑ i, u b j i = 1)
    (truth : (b : Fin 4) → Fin m → ℕ → Fin (size b) → ℝ) (error : ℝ)
    (hCap : ∀ b j t i, |(executedLoss theta (increment b j t i) : ℝ)| ≤ cap b)
    (hError : ∀ b j t i, |truth b j t i-(executedLoss theta (increment b j t i) : ℝ)| ≤ error)
    (T : ℕ) (hT : 0 < T) :
    (∑ b, weightedRegret v (geometricBase eta theta) (increment b) (truth b) (u b) T)/(T : ℝ) ≤
      4*((lambda : ℝ)+1)/((eta : ℝ)*T)+20*(eta : ℝ)+8*error := by
  have he := paper_regret size hSize lambda hAlphabet v hv hsv eta theta hEta hTheta hProduct
    increment u hu hsu truth error hCap hError T
  apply (div_le_iff₀ (by exact_mod_cast hT : (0 : ℝ) < T)).mpr
  calc
    _ ≤ 4*((lambda : ℝ)+1)/(eta : ℝ)+20*(eta : ℝ)*T+8*T*error := he
    _ = _ := by
      have ht : (T : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hT
      field_simp
      <;> ring

end Blotto.GeneralPaperFourBlockRegret
