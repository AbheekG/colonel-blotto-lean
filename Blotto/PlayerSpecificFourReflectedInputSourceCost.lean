import Blotto.PlayerSpecificFourReflectedInputFrameCost

/-! All reflected resource inputs are priced from the accepted original
four-row height; neither scaled size nor arithmetic cost is supplied. -/
namespace Blotto.PlayerSpecificFourReflectedInputSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := PlayerSpecificFourParameterSourceCost.coefficient*(H+25)^3+
  3*PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 13 H+14)^3+
  3*PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 13 H+14)^3+
  3*PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 14 H+14)^3+
  (4600*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 15 H+21)^3+32

theorem cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H : ℕ)
    (hm : Normalized r.root.polynomial) (hm0 : r.root.polynomial≠[]) (hml : r.root.polynomial.length≤4)
    (hmH : HasHeight r.root.polynomial H) (he : HasHeight [r.root.interval.lo,r.root.interval.hi] H)
    (hv : r.root.interval.lo<r.root.interval.hi) (hH : 2≤H) (ha : Fits r.root a H) :
    (PlayerSpecificFourReflectedInputExecution.run RationalCostModel.schoolbook r a).2≤work H := by
  let model:=RationalCostModel.schoolbook
  let root:=r.root
  let p:=parameters model root a
  let long:=PlayerSpecificAlgebraicFourReflectedInput.original a
  have h13:=PlayerSpecificAlgebraicExpressionBudget.initial_le 13 H
  have h14:=PlayerSpecificAlgebraicExpressionBudget.initial_le 14 H
  have h1314:=PlayerSpecificAlgebraicExpressionBudget.fuel_mono H (by omega : 13≤14)
  have hp (j : Fin 8) := parameter_bounds model root a H ha hm hm0 hml hmH hH j
  have hl:=PlayerSpecificAlgebraicFourReflectedSizes.original_bounds r a H ha
  have hscale13 : ∀ q z,Reduced root.polynomial q ∧ HasHeight q (iterate 13 H) →
      Reduced root.polynomial z ∧ HasHeight z H →
      (PlayerSpecificMixtureScalarExecution.scale model root q z).2≤
        PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 13 H+14)^3 := by
    intro q z hq hz
    exact PlayerSpecificMixtureScalarSourceCost.scale_cost root q z (iterate 13 H) hm hm0 hml
      (mono hmH h13) (mono he h13) hv hq ⟨hz.1,mono hz.2 h13⟩
  have hc (j : Fin 3) : Reduced root.polynomial (PlayerSpecificAlgebraicField.times root.polynomial (p.read 5) (long.read j)) ∧
      HasHeight (PlayerSpecificAlgebraicField.times root.polynomial (p.read 5) (long.read j)) (iterate 14 H) := by
    exact ⟨PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,
      times_height root.polynomial _ _ (iterate 13 H) hm hm0 hml (hp 5).1 (hl j).1
        (mono hmH h13) (hp 5).2 (mono (hl j).2 h13)⟩
  have hshort : (∑ j : Fin 3,(PlayerSpecificMixtureScalarExecution.scale model root (p.read 4) (long.read j)).2)≤
      3*PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 13 H+14)^3 := by
    calc
      _ ≤ ∑ _j : Fin 3,PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 13 H+14)^3 :=
        Finset.sum_le_sum (fun j _ => hscale13 _ _ (hp 4) (hl j))
      _ = _ := by simp [Nat.mul_assoc]
  have hcapacity : (∑ j : Fin 3,(PlayerSpecificMixtureScalarExecution.scale model root (p.read 5) (long.read j)).2)≤
      3*PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 13 H+14)^3 := by
    calc
      _ ≤ ∑ _j : Fin 3,PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 13 H+14)^3 :=
        Finset.sum_le_sum (fun j _ => hscale13 _ _ (hp 5) (hl j))
      _ = _ := by simp [Nat.mul_assoc]
  have hinitial : (∑ j : Fin 3,(PlayerSpecificMixtureScalarExecution.scale model root (p.read 6)
      (PlayerSpecificAlgebraicField.times root.polynomial (p.read 5) (long.read j))).2)≤
      3*PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 14 H+14)^3 := by
    calc
      _ ≤ ∑ _j : Fin 3,PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 14 H+14)^3 := by
        apply Finset.sum_le_sum
        intro j _
        exact PlayerSpecificMixtureScalarSourceCost.scale_cost root (p.read 6) _ (iterate 14 H) hm hm0 hml
          (mono hmH h14) (mono he h14) hv
          ⟨(hp 6).1,mono (hp 6).2 h1314⟩ (hc j)
      _ = _ := by simp [Nat.mul_assoc]
  have hparameter:=PlayerSpecificFourParameterSourceCost.cost root a H hm hm0 hml hmH he hv hH ha
  have hframe:=PlayerSpecificFourReflectedInputFrameCost.cost r a H hm hm0 hml hmH he hH ha
  rw [PlayerSpecificFourReflectedInputExecution.price_equation]
  unfold work
  refine Nat.add_le_add_right ?_ 32
  refine Nat.add_le_add ?_ hframe
  refine Nat.add_le_add ?_ hinitial
  refine Nat.add_le_add ?_ hcapacity
  exact Nat.add_le_add hparameter hshort

end Blotto.PlayerSpecificFourReflectedInputSourceCost
