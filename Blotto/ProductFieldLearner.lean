import Blotto.ProductGibbsWeights

/-! The exact-product one-field rational update variant inherits the constructed
stochastic regret theorem over all feasible whole code tuples. Expanded action
vectors/equivalences occur only in the proof interface; costs and native sampler
transition laws must be joined separately. This variant rounds the multiplier
only; retained source algorithms also round the stored product on each update. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

def computedFieldMultiplier {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ :=
  fun h x code => expMultiplierNative (eta * localLoss h x code) theta

noncomputable def liftedLocalLoss {a m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ) :
    List (Fin a) → Fin a → Fin (Fintype.card (FeasibleCodes bids budget)) → ℚ :=
  fun h x i => localLoss h x (((feasibleEquiv bids budget).symm i).val (selected h x))

theorem computedFieldHistory_dense_refinement {a m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (past : List (Fin a)) :
    feasibleVector bids budget (fieldHistory selected (computedFieldMultiplier selected localLoss eta theta) past) =
      rationalHistory (computedHistoryMultipliers (liftedLocalLoss bids budget selected localLoss) eta theta) past :=
  fieldHistory_dense_refinement bids budget selected _ past

theorem computedFieldHistory_expected_regret {a m : ℕ} {sizes : Fin m → ℕ}
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
        (fun h => normalizedReal (feasibleVector bids budget
          (fieldHistory selected (computedFieldMultiplier selected localLoss eta theta) h)))
        (selectedComparator past) past) ≤
      2 * Real.log (Fintype.card (FeasibleCodes bids budget)) + (eta : ℝ) ^ 2 / 2 * T *
        ((1 + 2 * (theta : ℝ) / (eta : ℝ)) ^ 2 + 1) + 2 * (theta : ℝ) * T := by
  simp_rw [computedFieldHistory_dense_refinement]
  exact computedHistory_expected_regret (feasibleCard_positive bids budget fallback hf) transition hp hs
    (liftedLocalLoss bids budget selected localLoss) eta theta heta ht (fun h x i => hl h x _) T selectedComparator hSelected

end SparseMW
end Blotto
