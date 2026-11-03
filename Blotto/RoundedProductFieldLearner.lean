import Blotto.AdaptivePerturbedRegret
import Blotto.ProductFieldLearner

/-! The source-style accumulated-product rounding history has the proved
conditional-direction regret bound. Stored mantissas are reset each changed
entry; the remaining sampler/objective/cost joins are explicit. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

theorem roundedProductField_expected_regret {a m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ h x, 0 ≤ transition h x) (hs : ∀ h, ∑ x, transition h x = 1)
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x code, 0 ≤ localLoss h x code ∧ localLoss h x code ≤ 1) (T : ℕ)
    (selectedComparator : List (Fin a) → Fin (Fintype.card (FeasibleCodes bids budget)) → ℝ)
    (hSelected : ∀ h, selectedComparator h ∈ simplexComparators (Fintype.card (FeasibleCodes bids budget))) :
    (eta : ℝ) * historyMean transition T (fun past =>
      cumulativePairing (fun h _x i => conditionalDirection transition
        (fun h x i => (liftedLocalLoss bids budget selected localLoss h x i : ℝ)) h i)
        (fun h => normalizedReal (feasibleVector bids budget (roundedFieldHistory selected localLoss eta theta h)))
        (selectedComparator past) past) ≤
      2 * Real.log (Fintype.card (FeasibleCodes bids budget)) + (eta : ℝ) ^ 2 / 2 * T *
        ((1 + 3 * (theta : ℝ) / (eta : ℝ)) ^ 2 + 1) + 3 * (theta : ℝ) * T := by
  let ratios := actionHistoryMultiplier bids budget selected (roundedFieldRatio selected localLoss eta theta)
  let losses := fun h x i => (liftedLocalLoss bids budget selected localLoss h x i : ℝ)
  have hetaR : (0 : ℝ) < (eta : ℝ) := by exact_mod_cast heta.1
  have hunit : ∀ h x i, 0 < ratios h x i ∧ ratios h x i ≤ 1 := by
    intro h x i
    apply storedRatio_unit
    · exact roundedFieldHistory_positive selected localLoss eta theta heta ht hl h _ _
    · exact ⟨mul_nonneg heta.1.le (hl h x _).1,
        (mul_le_of_le_one_right heta.1.le (hl h x _).2).trans heta.2⟩
    · exact ht
  have hloss : ∀ h x i, 0 ≤ losses h x i ∧ losses h x i ≤ 1 := by
    intro h x i
    change (0 : ℝ) ≤ (localLoss h x _ : ℝ) ∧ (localLoss h x _ : ℝ) ≤ 1
    exact ⟨by exact_mod_cast (hl h x _).1, by exact_mod_cast (hl h x _).2⟩
  have hperturb : ∀ h x i, losses h x i ≤ effectiveLoss (eta : ℝ) (ratios h x i : ℝ) ∧
      effectiveLoss (eta : ℝ) (ratios h x i : ℝ) ≤ losses h x i + 3 * (theta : ℝ) / (eta : ℝ) := by
    intro h x i
    apply storedRatio_effectiveLoss
    · exact roundedFieldHistory_positive selected localLoss eta theta heta ht hl h _ _
    · exact heta.1
    · exact ⟨mul_nonneg heta.1.le (hl h x _).1,
        (mul_le_of_le_one_right heta.1.le (hl h x _).2).trans heta.2⟩
    · exact ht
  have he := rationalHistory_expected_original_regret (feasibleCard_positive bids budget fallback hf) transition hp hs
    ratios losses (eta : ℝ) (3 * (theta : ℝ) / (eta : ℝ)) hetaR (fun h x i => (hunit h x i).1)
    (fun h x i => (hunit h x i).2) hloss hperturb T selectedComparator hSelected
  simp_rw [roundedFieldHistory_dense_refinement bids budget selected localLoss eta theta heta ht hl]
  dsimp [ratios, losses] at he
  have hcancel : (eta : ℝ) * T * (3 * (theta : ℝ) / (eta : ℝ)) = 3 * (theta : ℝ) * T := by field_simp
  rw [hcancel] at he
  exact he

theorem roundedProductField_entropy_regret {a m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (N : ℕ) (hN : 0 < N) (hsizes : ∀ j, sizes j ≤ N)
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ h x, 0 ≤ transition h x) (hs : ∀ h, ∑ x, transition h x = 1)
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x code, 0 ≤ localLoss h x code ∧ localLoss h x code ≤ 1) (T : ℕ)
    (selectedComparator : List (Fin a) → Fin (Fintype.card (FeasibleCodes bids budget)) → ℝ)
    (hSelected : ∀ h, selectedComparator h ∈ simplexComparators (Fintype.card (FeasibleCodes bids budget))) :
    (eta : ℝ) * historyMean transition T (fun past =>
      cumulativePairing (fun h _x i => conditionalDirection transition
        (fun h x i => (liftedLocalLoss bids budget selected localLoss h x i : ℝ)) h i)
        (fun h => normalizedReal (feasibleVector bids budget (roundedFieldHistory selected localLoss eta theta h)))
        (selectedComparator past) past) ≤
      2 * (m : ℝ) * Real.log N + (eta : ℝ) ^ 2 / 2 * T *
        ((1 + 3 * (theta : ℝ) / (eta : ℝ)) ^ 2 + 1) + 3 * (theta : ℝ) * T := by
  have he := roundedProductField_expected_regret bids budget fallback hf transition hp hs selected localLoss
    eta theta heta ht hl T selectedComparator hSelected
  have hc := feasibleEntropy_bound bids budget fallback hf N hN hsizes
  linarith

end SparseMW
end Blotto
