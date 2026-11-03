import Blotto.PlayerSpecificSegmentSelectionFramePolynomial

/-! Derived quotient, exact coin and rejection-difference source
prices for each actually reached segment-selection node. -/
namespace Blotto.PlayerSpecificSegmentSelectionNodeCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificSegmentSelectionSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem probability (root : Candidate) (weight remaining : Data) (S H slots : ℕ) (bits : Fin H → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmS : HasHeight root.polynomial S) (he : HasHeight [root.interval.lo,root.interval.hi] S) (hv : root.interval.lo<root.interval.hi)
    (hw : Reduced root.polynomial weight ∧ HasHeight weight S) (hr : Reduced root.polynomial remaining ∧ HasHeight remaining S) (hS : 1≤S) :
    let p:=PlayerSpecificFieldDivisionExecution.run RationalCostModel.schoolbook root.polynomial weight remaining
    Reduced root.polynomial p.1 ∧ HasHeight p.1 (PlayerSpecificAlgebraicHeightEnvelope.step S) ∧
      p.2≤(8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(size S H slots+1)^3 ∧
      (PlayerSpecificAlgebraicCoinExecution.run RationalCostModel.schoolbook root p.1 H bits).2≤
        PlayerSpecificAlgebraicCoinCost.polynomialCoefficient*(size S H slots+1)^3 := by
  let model:=RationalCostModel.schoolbook
  let p:=PlayerSpecificFieldDivisionExecution.run model root.polynomial weight remaining
  let U:=size S H slots
  have hlow:=lower S H slots
  have hp : Reduced root.polynomial p.1 := by
    rw [PlayerSpecificFieldDivisionExecution.value]
    exact PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0
  have hpH : HasHeight p.1 (PlayerSpecificAlgebraicHeightEnvelope.step S) := by
    rw [PlayerSpecificFieldDivisionExecution.value]
    exact PlayerSpecificAlgebraicHeightEnvelope.divide_height _ _ _ S hm hm0 hml hw.1 hr.1 hmS hw.2 hr.2 hS
  have hd:=(PlayerSpecificAlgebraicInitialPrimitiveCost.division_cost model root.polynomial weight remaining S hm hm0 hml
    hw.1 hr.1 hmS hw.2 hr.2 hS).trans
    (Nat.mul_le_mul_left _ (model.monotone ((PlayerSpecificAlgebraicExpressionPrimitiveCost.initial_width S).trans (width_mono hlow.1))))
  have hdc:=hd.trans (rational_polynomial 8000000000 U)
  have hstep:=PlayerSpecificAlgebraicHeightEnvelope.large S
  have hc:=PlayerSpecificAlgebraicCoinCost.cost root p.1 (PlayerSpecificAlgebraicHeightEnvelope.step S) H bits hm hm0 hml
    (mono hmS (by omega)) (mono he (by omega)) hv hpH hp
  have hc':=hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (show PlayerSpecificAlgebraicHeightEnvelope.step S+H+3≤U+1 by dsimp [U,size]; omega) 3))
  exact ⟨hp,hpH,hdc,hc'⟩

theorem difference (root : Candidate) (remaining weight : Data) (S H slots : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmS : HasHeight root.polynomial S) (hr : Reduced root.polynomial remaining ∧ HasHeight remaining S)
    (hw : Reduced root.polynomial weight ∧ HasHeight weight S) (hS : 1≤S) :
    price RationalCostModel.schoolbook (PlayerSpecificFieldCombination.run true root.polynomial remaining weight).2≤
      (200000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(size S H slots+1)^3 := by
  let model:=RationalCostModel.schoolbook
  have hlow:=lower S H slots
  have hrl : remaining.length≤3 := by have h:=hr.1.2; omega
  have hwl : weight.length≤3 := by have h:=hw.1.2; omega
  have hd:=(PlayerSpecificFieldCombinationCost.run_cost model true root.polynomial remaining weight hm hm0 hml S hmS hr.2 hw.2 hS hrl hwl).trans
    (Nat.mul_le_mul_left _ (model.monotone ((PlayerSpecificAlgebraicExpressionPrimitiveCost.combination_width S).trans (width_mono hlow.1))))
  exact hd.trans (rational_polynomial 200000000 (size S H slots))

end Blotto.PlayerSpecificSegmentSelectionNodeCost
