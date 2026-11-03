import Blotto.ProductFiniteTraining
import Blotto.ProductGibbsWeights

/-! The constrained product Gibbs vector supplies the finite whole-row training
law. Positive local fields normalize over exactly the feasible code tuples;
the semantic vector is used for proofs, not claimed as stored Cartesian data.
One exact local multiplier update and each adaptive field history have the normalized
entropy interpretation. Native compact sampling and its costs remain separate. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators Classical
namespace SparseMW

noncomputable def gibbsWholeRowLaw {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (hw : ∀ j code, 0 < weights j code) :
    RationalWholeRowLaw (Fintype.card (FeasibleCodes bids budget)) m where
  weight := normalizeQ (feasibleVector bids budget weights)
  nonnegative := fun i => (normalizeQ_positive (feasibleCard_positive bids budget fallback hf)
    _ (feasibleVector_positive bids budget weights hw) i).le
  sum_one := normalizeQ_sum (feasibleCard_positive bids budget fallback hf)
    _ (feasibleVector_positive bids budget weights hw)
  row := fun i j => bids j (((feasibleEquiv bids budget).symm i).val j)

theorem gibbsWholeRowLaw_realWeight {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (hw : ∀ j code, 0 < weights j code) :
    (gibbsWholeRowLaw bids budget fallback hf weights hw).realWeight =
      normalizedReal (feasibleVector bids budget weights) := rfl

theorem gibbsWholeRowLaw_row_feasible {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (hw : ∀ j code, 0 < weights j code)
    (hb : ∀ j code, 0 ≤ bids j code) (i : Fin (Fintype.card (FeasibleCodes bids budget))) :
    Feasible (budget : ℝ) ((gibbsWholeRowLaw bids budget fallback hf weights hw).realRow i) :=
  feasibleRow_hardBudget bids budget hb ((feasibleEquiv bids budget).symm i)

theorem gibbsWholeRowLaw_supported {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (hw : ∀ j code, 0 < weights j code)
    (hb : ∀ j code, 0 ≤ bids j code) :
    Supported (budget : ℝ) (gibbsWholeRowLaw bids budget fallback hf weights hw).law :=
  RationalWholeRowLaw.law_supported _ _ (gibbsWholeRowLaw_row_feasible bids budget fallback hf weights hw hb)

theorem gibbsWholeRowLaw_update_entropy {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (hw : ∀ j code, 0 < weights j code)
    (selected : Fin m) (multiplier : Fin (sizes selected) → ℚ) (hm : ∀ code, 0 < multiplier code)
    (eta : ℝ) (heta : eta ≠ 0) :
    (gibbsWholeRowLaw bids budget fallback hf (updateField weights selected multiplier)
      (updateField_positive weights selected multiplier hw hm)).realWeight =
      normalizedUpdate (gibbsWholeRowLaw bids budget fallback hf weights hw).realWeight
        (fun i => effectiveLoss eta (multiplier (((feasibleEquiv bids budget).symm i).val selected) : ℝ)) eta :=
  feasibleVector_normalized_update bids budget fallback hf weights selected multiplier hw hm eta heta

noncomputable def fieldHistoryWholeRowLaw {a m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (selected : List (Fin a) → Fin a → Fin m)
    (multiplier : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (hm : ∀ h x code, 0 < multiplier h x code) (past : List (Fin a)) :
    RationalWholeRowLaw (Fintype.card (FeasibleCodes bids budget)) m :=
  gibbsWholeRowLaw bids budget fallback hf (fieldHistory selected multiplier past)
    (fieldHistory_positive selected multiplier hm past)

theorem fieldHistoryWholeRowLaw_dense_refinement {a m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (selected : List (Fin a) → Fin a → Fin m)
    (multiplier : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (hm : ∀ h x code, 0 < multiplier h x code) (past : List (Fin a)) :
    (fieldHistoryWholeRowLaw bids budget fallback hf selected multiplier hm past).realWeight =
      normalizedReal (rationalHistory (actionHistoryMultiplier bids budget selected multiplier) past) := by
  rw [fieldHistoryWholeRowLaw, gibbsWholeRowLaw_realWeight, fieldHistory_dense_refinement]

theorem fieldHistoryWholeRowLaw_supported {a m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (selected : List (Fin a) → Fin a → Fin m)
    (multiplier : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (hm : ∀ h x code, 0 < multiplier h x code) (hb : ∀ j code, 0 ≤ bids j code) (past : List (Fin a)) :
    Supported (budget : ℝ) (fieldHistoryWholeRowLaw bids budget fallback hf selected multiplier hm past).law :=
  gibbsWholeRowLaw_supported bids budget fallback hf _ (fieldHistory_positive selected multiplier hm past) hb

theorem gibbsTraining_conditional_loss {m r : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (hw : ∀ j code, 0 < weights j code)
    (own : RationalWholeRowLaw r m) (values : RationalFieldSelector m) (candidate : Allocation m) :
    (∑ observed, (ProductFiniteTraining.indexedProbability own
      (gibbsWholeRowLaw bids budget fallback hf weights hw) values observed : ℝ) *
      ProductFiniteTraining.empiricalLossA (gibbsWholeRowLaw bids budget fallback hf weights hw) candidate
        ((ProductFiniteTraining.observationEquiv r (Fintype.card (FeasibleCodes bids budget)) m).symm observed)) =
      purePayoff values.values candidate (gibbsWholeRowLaw bids budget fallback hf weights hw).law :=
  ProductFiniteTraining.indexed_conditionalLossA own _ values candidate

theorem gibbsTraining_transition_sum {m : ℕ} {sizesA sizesB : Fin m → ℕ}
    (bidsA : (j : Fin m) → Fin (sizesA j) → ℚ) (budgetA : ℚ)
    (fallbackA : ProductCodes sizesA) (hfA : productResource bidsA fallbackA ≤ budgetA)
    (weightsA : (j : Fin m) → Fin (sizesA j) → ℚ) (hwA : ∀ j code, 0 < weightsA j code)
    (bidsB : (j : Fin m) → Fin (sizesB j) → ℚ) (budgetB : ℚ)
    (fallbackB : ProductCodes sizesB) (hfB : productResource bidsB fallbackB ≤ budgetB)
    (weightsB : (j : Fin m) → Fin (sizesB j) → ℚ) (hwB : ∀ j code, 0 < weightsB j code)
    (values : RationalFieldSelector m) :
    ∑ observed, ProductFiniteTraining.indexedProbability
      (gibbsWholeRowLaw bidsA budgetA fallbackA hfA weightsA hwA)
      (gibbsWholeRowLaw bidsB budgetB fallbackB hfB weightsB hwB) values observed = 1 :=
  ProductFiniteTraining.indexedProbability_sum _ _ values

theorem gibbsTraining_opposing_loss {m r : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (budget : ℚ)
    (fallback : ProductCodes sizes) (hf : productResource bids fallback ≤ budget)
    (weights : (j : Fin m) → Fin (sizes j) → ℚ) (hw : ∀ j code, 0 < weights j code)
    (own : RationalWholeRowLaw r m) (values : RationalFieldSelector m) (candidate : Allocation m) :
    (∑ observed, (ProductFiniteTraining.indexedProbability own
      (gibbsWholeRowLaw bids budget fallback hf weights hw) values observed : ℝ) *
      ProductFiniteTraining.opposingLossA (gibbsWholeRowLaw bids budget fallback hf weights hw) candidate
        ((ProductFiniteTraining.observationEquiv r (Fintype.card (FeasibleCodes bids budget)) m).symm observed)) =
      1 - purePayoff values.values candidate (gibbsWholeRowLaw bids budget fallback hf weights hw).law :=
  ProductFiniteTraining.indexed_conditionalOpposingLossA own _ values candidate

-- Histories select complete player laws; their product with the field law is
-- normalized at every past. This is the transition contract for finite adaptive
-- expectation, without claiming a compact native implementation of the arrays.
noncomputable def adaptiveTrainingTransition {a r s m : ℕ}
    (lawA : List (Fin a) → RationalWholeRowLaw r m)
    (lawB : List (Fin a) → RationalWholeRowLaw s m) (values : RationalFieldSelector m)
    (past : List (Fin a)) (observed : Fin (r * (s * m))) : ℝ :=
  ProductFiniteTraining.indexedProbability (lawA past) (lawB past) values observed

theorem adaptiveTrainingTransition_nonnegative {a r s m : ℕ}
    (lawA : List (Fin a) → RationalWholeRowLaw r m)
    (lawB : List (Fin a) → RationalWholeRowLaw s m) (values : RationalFieldSelector m)
    (past : List (Fin a)) (observed : Fin (r * (s * m))) :
    0 ≤ adaptiveTrainingTransition lawA lawB values past observed := by
  unfold adaptiveTrainingTransition
  exact_mod_cast ProductFiniteTraining.indexedProbability_nonnegative (lawA past) (lawB past) values observed

theorem adaptiveTrainingTransition_sum {a r s m : ℕ}
    (lawA : List (Fin a) → RationalWholeRowLaw r m)
    (lawB : List (Fin a) → RationalWholeRowLaw s m) (values : RationalFieldSelector m)
    (past : List (Fin a)) : ∑ observed, adaptiveTrainingTransition lawA lawB values past observed = 1 := by
  unfold adaptiveTrainingTransition
  exact_mod_cast ProductFiniteTraining.indexedProbability_sum (lawA past) (lawB past) values

theorem adaptiveTrainingTransition_opposing_mean {a r s m : ℕ}
    (lawA : List (Fin a) → RationalWholeRowLaw r m)
    (lawB : List (Fin a) → RationalWholeRowLaw s m) (values : RationalFieldSelector m)
    (past : List (Fin a)) (candidate : Allocation m) :
    (∑ observed, adaptiveTrainingTransition lawA lawB values past observed *
      ProductFiniteTraining.opposingLossA (lawB past) candidate
        ((ProductFiniteTraining.observationEquiv r s m).symm observed)) =
      1 - purePayoff values.values candidate (lawB past).law :=
  ProductFiniteTraining.indexed_conditionalOpposingLossA (lawA past) (lawB past) values candidate

noncomputable def trainingHistoryTransition {r s m : ℕ}
    (lawA : List (Fin (r * (s * m))) → RationalWholeRowLaw r m)
    (lawB : List (Fin (r * (s * m))) → RationalWholeRowLaw s m) (values : RationalFieldSelector m) :
    List (Fin (r * (s * m))) → Fin (r * (s * m)) → ℝ :=
  adaptiveTrainingTransition lawA lawB values

theorem trainingHistoryTransition_normalized {r s m : ℕ}
    (lawA : List (Fin (r * (s * m))) → RationalWholeRowLaw r m)
    (lawB : List (Fin (r * (s * m))) → RationalWholeRowLaw s m) (values : RationalFieldSelector m) :
    (∀ past observed, 0 ≤ trainingHistoryTransition lawA lawB values past observed) ∧
      (∀ past, ∑ observed, trainingHistoryTransition lawA lawB values past observed = 1) :=
  ⟨adaptiveTrainingTransition_nonnegative lawA lawB values, adaptiveTrainingTransition_sum lawA lawB values⟩

end SparseMW
end Blotto
