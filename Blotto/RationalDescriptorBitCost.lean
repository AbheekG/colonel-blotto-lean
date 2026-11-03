import Blotto.RationalLocalFormulaBitCost

/-! Complete local descriptors have constant Rat(W)-priced formula work.
Weights and all endpoint coordinates are charged, even when some slots have
zero weight. Parent construction, allocation and sampler control are separate. -/

namespace Blotto
open scoped BigOperators

namespace RationalThreeGeometryCode

noncomputable def descriptorBitCost (model : RationalCostModel) (g : RationalThreeGeometry) : ℕ :=
  (∑ slot : Fin 9, (chosen slot).bitCost model (environment g)) +
    (∑ slot : Fin 9, ∑ j : Fin 3, (vertex (threeEdges slot).1 j).bitCost model (environment g)) +
    (∑ slot : Fin 9, ∑ j : Fin 3, (vertex (threeEdges slot).2 j).bitCost model (environment g))

theorem descriptorBitCost_bound (model : RationalCostModel) (g : RationalThreeGeometry)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    descriptorBitCost model g ≤ 2736 * model.rat (1 + 2 * expressionHeightBudget s 16) := by
  let price := model.rat (1 + 2 * expressionHeightBudget s 16)
  have hw : (∑ slot : Fin 9, (chosen slot).bitCost model (environment g)) ≤ 9 * (256 * price) := by
    calc
      _ ≤ ∑ _slot : Fin 9, 256 * price := Finset.sum_le_sum (fun slot _ => chosen_bitCost model g slot s hs hEnv)
      _ = _ := by simp
  have hp : (∑ slot : Fin 9, ∑ j : Fin 3, (vertex (threeEdges slot).1 j).bitCost model (environment g)) ≤ 9 * (3 * (8 * price)) := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 3, 8 * price :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => vertex_bitCost model g _ j s hs hEnv))
      _ = _ := by simp
  have hq : (∑ slot : Fin 9, ∑ j : Fin 3, (vertex (threeEdges slot).2 j).bitCost model (environment g)) ≤ 9 * (3 * (8 * price)) := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 3, 8 * price :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => vertex_bitCost model g _ j s hs hEnv))
      _ = _ := by simp
  change descriptorBitCost model g ≤ 2736 * price
  unfold descriptorBitCost
  omega

end RationalThreeGeometryCode
namespace RationalNestedParametersCode

def scalarBitCost (model : RationalCostModel) (i : RationalNestedInput) (x : ℚ) : ℕ :=
  ∑ j : Fin 6, (scalarPrograms j).bitCost model (environment i x)

theorem scalarBitCost_bound (model : RationalCostModel) (i : RationalNestedInput) (x : ℚ)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ k, RationalHeight ((environment i x).read k) s) :
    scalarBitCost model i x ≤ 768 * model.rat (1 + 2 * expressionHeightBudget s 8) := by
  calc
    _ ≤ ∑ _j : Fin 6, 128 * model.rat (1 + 2 * expressionHeightBudget s 8) :=
      Finset.sum_le_sum (fun j _ => scalar_bitCost model i x j s hs hEnv)
    _ = _ := by simp; ring

end RationalNestedParametersCode
namespace RationalFourParametersCode

def parametersBitCost (model : RationalCostModel) (i : RationalFourInput) : ℕ :=
  ∑ j : Fin 8, (programs j).bitCost model (environment i)

theorem parametersBitCost_bound (model : RationalCostModel) (i : RationalFourInput)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ k, RationalHeight ((environment i).read k) s) :
    parametersBitCost model i ≤ 2048 * model.rat (1 + 2 * expressionHeightBudget s 12) := by
  calc
    _ ≤ ∑ _j : Fin 8, 256 * model.rat (1 + 2 * expressionHeightBudget s 12) :=
      Finset.sum_le_sum (fun j _ => parameter_bitCost model i j s hs hEnv)
    _ = _ := by simp; ring

end RationalFourParametersCode
namespace RationalOverlapFormula
open OverlapFormulaCode

def descriptorBitCost {k h : ℕ} (model : RationalCostModel) (G : RationalOverlapGluing k h) (B : ℚ) : ℕ :=
  (∑ slot : Fin (k * h), weight.bitCost model (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) +
    (∑ slot : Fin (k * h), ∑ r : Fin 4, (safeP r).bitCost model (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) +
    (∑ slot : Fin (k * h), ∑ r : Fin 4, (safeQ r).bitCost model (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2))

theorem descriptorBitCost_bound {k h : ℕ} (model : RationalCostModel) (G : RationalOverlapGluing k h) (B : ℚ)
    (s : ℕ) (hs : 2 ≤ s) (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    descriptorBitCost model G B ≤ 2176 * (k * h) * model.rat (1 + 2 * expressionHeightBudget s 9) := by
  let price := model.rat (1 + 2 * expressionHeightBudget s 9)
  have hw : (∑ slot : Fin (k * h), weight.bitCost model (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) ≤ (k * h) * (128 * price) := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), 128 * price :=
        Finset.sum_le_sum (fun slot _ => weight_bitCost model G B _ _ s hs hFirst hSecond hD hB)
      _ = _ := by simp
  have hp : (∑ slot : Fin (k * h), ∑ r : Fin 4, (safeP r).bitCost model (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) ≤ (k * h) * (4 * (256 * price)) := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), ∑ _r : Fin 4, 256 * price :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun r _ => safeP_bitCost model G B _ _ s hs hFirst hSecond hD hB r))
      _ = _ := by simp
  have hq : (∑ slot : Fin (k * h), ∑ r : Fin 4, (safeQ r).bitCost model (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)) ≤ (k * h) * (4 * (256 * price)) := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), ∑ _r : Fin 4, 256 * price :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun r _ => safeQ_bitCost model G B _ _ s hs hFirst hSecond hD hB r))
      _ = _ := by simp
  change descriptorBitCost model G B ≤ 2176 * (k * h) * price
  unfold descriptorBitCost
  nlinarith

end RationalOverlapFormula
end Blotto
