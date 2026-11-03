import Blotto.ProductFieldWeights

/-! Sparse local fields represent a finite constrained Gibbs law. Its action
space consists exactly of whole code tuples satisfying the hard resource budget.
A one-field update multiplies each feasible action by its own computed local
multiplier, without enumerating that Cartesian action space in the field update. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

abbrev ProductCodes {m : ℕ} (sizes : Fin m → ℕ) := (j : Fin m) → Fin (sizes j)

def productMass {m : ℕ} {sizes : Fin m → ℕ}
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (code : ProductCodes sizes) : ℚ :=
  ∏ j, weights j (code j)

def productResource {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (code : ProductCodes sizes) : ℚ :=
  ∑ j, bids j (code j)

abbrev FeasibleCodes {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ) :=
  {code : ProductCodes sizes // productResource bids code ≤ budget}

def updateField {m : ℕ} {sizes : Fin m → ℕ}
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (selected : Fin m)
    (multiplier : Fin (sizes selected) → ℚ) : (j : Fin m) → Fin (sizes j) → ℚ :=
  Function.update weights selected (fun code => weights selected code * multiplier code)

theorem productMass_update {m : ℕ} {sizes : Fin m → ℕ}
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (selected : Fin m)
    (multiplier : Fin (sizes selected) → ℚ) (code : ProductCodes sizes) :
    productMass (updateField weights selected multiplier) code =
      productMass weights code * multiplier (code selected) := by
  have hpoint : (fun j => updateField weights selected multiplier j (code j)) =
      update (fun j => weights j (code j)) selected (multiplier (code selected)) := by
    funext j
    by_cases he : j = selected
    · subst j
      simp [updateField, update]
    · simp [updateField, update, he]
  unfold productMass
  rw [hpoint]
  exact update_product _ selected _

theorem productMass_positive {m : ℕ} {sizes : Fin m → ℕ}
    (weights : (j : Fin m) → Fin (sizes j) → ℚ)
    (hw : ∀ j code, 0 < weights j code) (code : ProductCodes sizes) :
    0 < productMass weights code :=
  Finset.prod_pos (fun j _ => hw j (code j))

theorem updateField_positive {m : ℕ} {sizes : Fin m → ℕ}
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (selected : Fin m)
    (multiplier : Fin (sizes selected) → ℚ)
    (hw : ∀ j code, 0 < weights j code) (hm : ∀ code, 0 < multiplier code) :
    ∀ j code, 0 < updateField weights selected multiplier j code := by
  intro j code
  by_cases he : j = selected
  · subst j
    simp only [updateField, Function.update_self]
    exact mul_pos (hw _ _) (hm _)
  · simp only [updateField, Function.update_of_ne he]
    exact hw j code

def feasibleMass {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (code : FeasibleCodes bids budget) : ℚ :=
  productMass weights code.val

theorem feasibleMass_update {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (selected : Fin m)
    (multiplier : Fin (sizes selected) → ℚ) (code : FeasibleCodes bids budget) :
    feasibleMass bids budget (updateField weights selected multiplier) code =
      feasibleMass bids budget weights code * multiplier (code.val selected) :=
  productMass_update weights selected multiplier code.val

noncomputable def feasibleEquiv {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ) :
    FeasibleCodes bids budget ≃ Fin (Fintype.card (FeasibleCodes bids budget)) := Fintype.equivFin _

noncomputable def feasibleVector {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) : Fin (Fintype.card (FeasibleCodes bids budget)) → ℚ :=
  fun i => feasibleMass bids budget weights ((feasibleEquiv bids budget).symm i)

theorem feasibleVector_update {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (selected : Fin m)
    (multiplier : Fin (sizes selected) → ℚ) :
    feasibleVector bids budget (updateField weights selected multiplier) =
      multiplyWeights (feasibleVector bids budget weights)
        (fun i => multiplier (((feasibleEquiv bids budget).symm i).val selected)) := by
  funext i
  exact feasibleMass_update bids budget weights selected multiplier _

theorem feasibleVector_positive {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (hw : ∀ j code, 0 < weights j code) :
    ∀ i, 0 < feasibleVector bids budget weights i := fun _i => productMass_positive weights hw _

theorem feasibleCard_positive {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ) (fallback : ProductCodes sizes)
    (hf : productResource bids fallback ≤ budget) : 0 < Fintype.card (FeasibleCodes bids budget) := by
  have hn : Nonempty (FeasibleCodes bids budget) := ⟨⟨fallback, hf⟩⟩
  exact Fintype.card_pos_iff.mpr hn

theorem feasibleVector_normalized_update {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (selected : Fin m)
    (multiplier : Fin (sizes selected) → ℚ)
    (hw : ∀ j code, 0 < weights j code) (hm : ∀ code, 0 < multiplier code) (eta : ℝ) (heta : eta ≠ 0) :
    normalizedReal (feasibleVector bids budget (updateField weights selected multiplier)) =
      normalizedUpdate (normalizedReal (feasibleVector bids budget weights))
        (fun i => effectiveLoss eta (multiplier (((feasibleEquiv bids budget).symm i).val selected) : ℝ)) eta := by
  rw [feasibleVector_update]
  exact normalizedReal_update (feasibleCard_positive bids budget fallback hf) _ _
    (feasibleVector_positive bids budget weights hw) (fun i => hm _) eta heta

theorem feasibleRow_hardBudget {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ) (hb : ∀ j code, 0 ≤ bids j code)
    (code : FeasibleCodes bids budget) :
    Feasible (budget : ℝ) (fun j => (bids j (code.val j) : ℝ)) := by
  constructor
  · intro j
    change (0 : ℝ) ≤ (bids j (code.val j) : ℝ)
    exact_mod_cast hb j (code.val j)
  · have he : (∑ j, (bids j (code.val j) : ℝ)) = (productResource bids code.val : ℝ) := by
      simp only [productResource, Rat.cast_sum]
    rw [he]
    exact_mod_cast code.property

def fieldHistory {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (multiplier : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ) :
    List (Fin a) → (j : Fin m) → Fin (sizes j) → ℚ
  | [] => fun _ _ => 1
  | x :: h => updateField (fieldHistory selected multiplier h) (selected h x) (multiplier h x)

noncomputable def actionHistoryMultiplier {a m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (selected : List (Fin a) → Fin a → Fin m)
    (multiplier : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ) :
    List (Fin a) → Fin a → Fin (Fintype.card (FeasibleCodes bids budget)) → ℚ :=
  fun h x i => multiplier h x (((feasibleEquiv bids budget).symm i).val (selected h x))

theorem fieldHistory_dense_refinement {a m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (selected : List (Fin a) → Fin a → Fin m)
    (multiplier : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (past : List (Fin a)) :
    feasibleVector bids budget (fieldHistory selected multiplier past) =
      rationalHistory (actionHistoryMultiplier bids budget selected multiplier) past := by
  induction past with
  | nil => funext i; simp [feasibleVector, feasibleMass, productMass, fieldHistory, rationalHistory]
  | cons x h ih =>
    rw [fieldHistory, feasibleVector_update, ih]
    rfl

theorem fieldHistory_positive {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (multiplier : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (hm : ∀ h x code, 0 < multiplier h x code) (past : List (Fin a)) :
    ∀ j code, 0 < fieldHistory selected multiplier past j code := by
  induction past with
  | nil => intro j code; norm_num [fieldHistory]
  | cons x h ih => exact updateField_positive _ _ _ ih (hm h x)

theorem feasibleCard_le_product {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ) :
    Fintype.card (FeasibleCodes bids budget) ≤ ∏ j, sizes j := by
  have he := Fintype.card_subtype_le (fun code : ProductCodes sizes => productResource bids code ≤ budget)
  simpa only [Fintype.card_pi, Fintype.card_fin] using he

theorem feasibleCard_le_power {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ) (N : ℕ)
    (hs : ∀ j, sizes j ≤ N) : Fintype.card (FeasibleCodes bids budget) ≤ N ^ m := by
  calc
    _ ≤ ∏ j, sizes j := feasibleCard_le_product bids budget
    _ ≤ ∏ _j : Fin m, N := Finset.prod_le_prod (fun j _ => hs j)
    _ = N ^ m := by simp

theorem feasibleEntropy_bound {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (N : ℕ) (_hN : 0 < N) (hs : ∀ j, sizes j ≤ N) :
    Real.log (Fintype.card (FeasibleCodes bids budget)) ≤ (m : ℝ) * Real.log N := by
  have hc : (0 : ℝ) < Fintype.card (FeasibleCodes bids budget) := by exact_mod_cast feasibleCard_positive bids budget fallback hf
  have hb : (Fintype.card (FeasibleCodes bids budget) : ℝ) ≤ (N : ℝ) ^ m := by
    exact_mod_cast feasibleCard_le_power bids budget N hs
  have he := Real.log_le_log hc hb
  rw [Real.log_pow] at he
  exact he

end SparseMW
end Blotto
