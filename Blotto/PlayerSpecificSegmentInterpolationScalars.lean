import Blotto.PlayerSpecificSegmentInterpolationSizes

/-! Both actual interpolation coefficients have sizes derived from the
original rational scalar. The rational complement is computed once. -/
namespace Blotto.PlayerSpecificSegmentInterpolationScalars
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificSegmentInterpolationSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem fits (root : Candidate) (q : ℚ) (T : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmT : HasHeight root.polynomial T) (hq : RationalHeight q T) (hT : 1≤T) :
    let complement:=scalar .subtract 1 q
    let left:=PlayerSpecificFieldCombinationContract.constant root.polynomial complement.1
    let right:=PlayerSpecificFieldCombinationContract.constant root.polynomial q
    RationalHeight complement.1 (base T) ∧
      (Reduced root.polynomial left.1 ∧ HasHeight left.1 (scalarHeight T)) ∧
      (Reduced root.polynomial right.1 ∧ HasHeight right.1 (scalarHeight T)) := by
  let complement:=scalar .subtract 1 q
  have hc : RationalHeight complement.1 (base T) := by
    change RationalHeight (1-q) (base T)
    exact ((one_height.mono hT).sub hq).mono (by dsimp [base]; omega)
  have hbase:=base_lower T
  dsimp only
  refine ⟨hc,?_,?_⟩
  · rw [PlayerSpecificFieldCombinationContract.constant_value]
    exact ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,
      PlayerSpecificAlgebraicHeightEnvelope.constant_height _ _ (base T) (mono hmT hbase.1) hc hbase.2 hml⟩
  · rw [PlayerSpecificFieldCombinationContract.constant_value]
    exact ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,
      PlayerSpecificAlgebraicHeightEnvelope.constant_height _ _ (base T) (mono hmT hbase.1) (hq.mono hbase.1) hbase.2 hml⟩

theorem setup_cost (root : Candidate) (q : ℚ) (T N slots : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmT : HasHeight root.polynomial T) (hq : RationalHeight q T) (hT : 1≤T) :
    let complement:=scalar .subtract 1 q
    price RationalCostModel.schoolbook complement.2+
      price RationalCostModel.schoolbook (PlayerSpecificFieldCombinationContract.constant root.polynomial complement.1).2+
      price RationalCostModel.schoolbook (PlayerSpecificFieldCombinationContract.constant root.polynomial q).2≤
        (400000015*PlayerSpecificResourceCostProfile.rationalCoefficient)*(height N slots T+16)^3 := by
  let model:=RationalCostModel.schoolbook
  let U:=height N slots T
  let S:=base T
  let complement:=scalar .subtract 1 q
  have hbase:=base_lower T
  have hSU : S≤U := (lower N slots T).1
  have hTU : T≤U := hbase.1.trans hSU
  have hcH:=(fits root q T hm hm0 hml hmT hq hT).1
  have hwidth : 4*T+3≤PlayerSpecificAlgebraicComparisonExecution.width U := by
    have hlarge:=(PlayerSpecificAlgebraicActiveListCost.width_large U).2.1
    dsimp [S,base] at hSU
    omega
  have hcFits:=fits_mono (scalar_fits_height .subtract 1 q T (one_height.mono hT) hq) hwidth
  have hcCost:=price_bound model (PlayerSpecificAlgebraicComparisonExecution.width U)
    (by have h:32≤PlayerSpecificAlgebraicComparisonExecution.width U:=(PlayerSpecificAlgebraicActiveListCost.width_large U).1; omega) _ hcFits
  simp only [scalar_length] at hcCost
  have hwidth':=(PlayerSpecificAlgebraicExpressionPrimitiveCost.initial_width S).trans (PlayerSpecificSegmentSelectionSizes.width_mono hSU)
  have hl:=(PlayerSpecificAlgebraicInitialPrimitiveCost.constant_cost model root.polynomial complement.1 S hm hm0 hml
    (mono hmT hbase.1) hcH hbase.2).trans (Nat.mul_le_mul_left _ (model.monotone hwidth'))
  have hr:=(PlayerSpecificAlgebraicInitialPrimitiveCost.constant_cost model root.polynomial q S hm hm0 hml
    (mono hmT hbase.1) (hq.mono hbase.1) hbase.2).trans (Nat.mul_le_mul_left _ (model.monotone hwidth'))
  have hs : price model complement.2+price model (PlayerSpecificFieldCombinationContract.constant root.polynomial complement.1).2+
      price model (PlayerSpecificFieldCombinationContract.constant root.polynomial q).2≤400000015*model.rat (PlayerSpecificAlgebraicComparisonExecution.width U) := by
    change price model complement.2≤15*model.rat (PlayerSpecificAlgebraicComparisonExecution.width U) at hcCost
    omega
  exact (hs.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 400000015 U)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : U+1≤U+16) 3))

end Blotto.PlayerSpecificSegmentInterpolationScalars
