import Blotto.ProductGibbsTraining
import Blotto.SparseMWStoredRounding

/-! Every changed local weight is rounded after multiplication; all other
fields are untouched. Effective ratios depend on the old local weight, and
its implicit feasible-action entropy update is derived exactly. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

def roundedFieldHistory {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) : List (Fin a) → (j : Fin m) → Fin (sizes j) → ℚ
  | [] => fun _ _ => 1
  | x :: h =>
      let old := roundedFieldHistory selected localLoss eta theta h
      Function.update old (selected h x)
        (fun code => storedUpdate (old (selected h x) code) eta (localLoss h x code) theta)

theorem roundedFieldHistory_positive {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x code, 0 ≤ localLoss h x code ∧ localLoss h x code ≤ 1) (past : List (Fin a)) :
    ∀ j code, 0 < roundedFieldHistory selected localLoss eta theta past j code := by
  induction past with
  | nil => intro j code; norm_num [roundedFieldHistory]
  | cons x h ih =>
    intro j code
    by_cases he : j = selected h x
    · subst j
      simp only [roundedFieldHistory, Function.update_self]
      exact storedUpdate_positive _ _ _ _ (ih _ _)
        ⟨mul_nonneg heta.1.le (hl h x code).1,
          (mul_le_of_le_one_right heta.1.le (hl h x code).2).trans heta.2⟩ ht
    · simp only [roundedFieldHistory, Function.update_of_ne he]
      exact ih j code

def roundedFieldRatio {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (h : List (Fin a)) (x : Fin a) (code : Fin (sizes (selected h x))) : ℚ :=
  storedRatio (roundedFieldHistory selected localLoss eta theta h (selected h x) code) eta (localLoss h x code) theta

theorem roundedFieldHistory_as_fieldHistory {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x code, 0 ≤ localLoss h x code ∧ localLoss h x code ≤ 1) (past : List (Fin a)) :
    roundedFieldHistory selected localLoss eta theta past =
      fieldHistory selected (roundedFieldRatio selected localLoss eta theta) past := by
  induction past with
  | nil => rfl
  | cons x h ih =>
    unfold roundedFieldHistory fieldHistory updateField
    rw [← ih]
    apply congrArg (Function.update (roundedFieldHistory selected localLoss eta theta h) (selected h x))
    funext code
    exact (storedUpdate_exact_ratio _ _ _ _ (ne_of_gt (roundedFieldHistory_positive selected localLoss eta theta heta ht hl h _ code))).symm

theorem roundedFieldHistory_dense_refinement {a m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x code, 0 ≤ localLoss h x code ∧ localLoss h x code ≤ 1) (past : List (Fin a)) :
    feasibleVector bids budget (roundedFieldHistory selected localLoss eta theta past) =
      rationalHistory (actionHistoryMultiplier bids budget selected (roundedFieldRatio selected localLoss eta theta)) past := by
  rw [roundedFieldHistory_as_fieldHistory selected localLoss eta theta heta ht hl]
  exact fieldHistory_dense_refinement bids budget selected _ past

theorem roundedFieldHistory_decreases {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x code, 0 ≤ localLoss h x code ∧ localLoss h x code ≤ 1)
    (h : List (Fin a)) (x : Fin a) (j : Fin m) (code : Fin (sizes j)) :
    roundedFieldHistory selected localLoss eta theta (x :: h) j code ≤
      roundedFieldHistory selected localLoss eta theta h j code := by
  by_cases he : j = selected h x
  · subst j
    simp only [roundedFieldHistory, Function.update_self]
    exact storedUpdate_decreases _ _ _ _ (roundedFieldHistory_positive selected localLoss eta theta heta ht hl h _ _)
      ⟨mul_nonneg heta.1.le (hl h x code).1,
        (mul_le_of_le_one_right heta.1.le (hl h x code).2).trans heta.2⟩ ht
  · simp only [roundedFieldHistory, Function.update_of_ne he, le_refl]

theorem roundedFieldHistory_le_one {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x code, 0 ≤ localLoss h x code ∧ localLoss h x code ≤ 1) (past : List (Fin a)) :
    ∀ j code, roundedFieldHistory selected localLoss eta theta past j code ≤ 1 := by
  induction past with
  | nil => intro j code; exact le_rfl
  | cons x past ih => intro j code; exact
    (roundedFieldHistory_decreases selected localLoss eta theta heta ht hl past x j code).trans (ih j code)

def fieldUpdateCount {a m : ℕ} (selected : List (Fin a) → Fin a → Fin m) : List (Fin a) → Fin m → ℕ
  | [] => fun _ => 0
  | x :: h => fun j => fieldUpdateCount selected h j + if j = selected h x then 1 else 0

theorem fieldUpdateCount_sum {a m : ℕ} (selected : List (Fin a) → Fin a → Fin m)
    (past : List (Fin a)) : (∑ j, fieldUpdateCount selected past j) = past.length := by
  induction past with
  | nil => simp [fieldUpdateCount]
  | cons x past ih => simp [fieldUpdateCount, Finset.sum_add_distrib, ih]

theorem roundedFieldHistory_exp_lower {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x code, 0 ≤ localLoss h x code ∧ localLoss h x code ≤ 1) (past : List (Fin a)) :
    ∀ j code, Real.exp (-(fieldUpdateCount selected past j : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ))) ≤
      (roundedFieldHistory selected localLoss eta theta past j code : ℝ) := by
  induction past with
  | nil => intro j code; simp [fieldUpdateCount, roundedFieldHistory]
  | cons x h ih =>
    intro j code
    by_cases hj : j = selected h x
    · subst j
      have hOld := roundedFieldHistory_positive selected localLoss eta theta heta ht hl h _ code
      have hx : 0 ≤ eta * localLoss h x code ∧ eta * localLoss h x code ≤ 1 / 4 :=
        ⟨mul_nonneg heta.1.le (hl h x code).1,
          (mul_le_of_le_one_right heta.1.le (hl h x code).2).trans heta.2⟩
      have hc := (storedRatio_certificate _ _ _ _ hOld hx ht).1
      have hLoss : (eta : ℝ) * (localLoss h x code : ℝ) ≤ (eta : ℝ) := by
        exact_mod_cast mul_le_of_le_one_right heta.1.le (hl h x code).2
      have hDecay : Real.exp (-((eta : ℝ) + 3 * (theta : ℝ))) ≤
          (storedRatio (roundedFieldHistory selected localLoss eta theta h (selected h x) code) eta
            (localLoss h x code) theta : ℝ) :=
        (Real.exp_le_exp.mpr (by linarith)).trans hc
      have hProduct := mul_le_mul (ih _ code) hDecay (Real.exp_pos _).le (by exact_mod_cast hOld.le)
      have hExact := storedUpdate_exact_ratio _ eta (localLoss h x code) theta (ne_of_gt hOld)
      have hExactR : (roundedFieldHistory selected localLoss eta theta h (selected h x) code : ℝ) *
          (storedRatio (roundedFieldHistory selected localLoss eta theta h (selected h x) code) eta
            (localLoss h x code) theta : ℝ) =
          (storedUpdate (roundedFieldHistory selected localLoss eta theta h (selected h x) code) eta (localLoss h x code) theta : ℝ) := by
        exact_mod_cast hExact
      rw [hExactR, ← Real.exp_add] at hProduct
      simp only [fieldUpdateCount, ite_true, Nat.cast_add, Nat.cast_one, roundedFieldHistory, Function.update_self]
      convert hProduct using 1
      congr 1
      ring
    · simp only [fieldUpdateCount, hj, ite_false, Nat.add_zero, roundedFieldHistory, Function.update_of_ne hj]
      exact ih j code

end SparseMW
end Blotto
