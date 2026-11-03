import Blotto.PlayerSpecificNestedThirdProfileExecution

/-! Complete third profile source prices, including its residual,
exact branch test, selected-only family and mixture/padding assembly. -/
namespace Blotto.PlayerSpecificNestedThirdProfileSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def residualWork (H : ℕ) : ℕ := PlayerSpecificResidualTableSourceCost.coefficient*(H+1)^3+
  PlayerSpecificDescriptorPadSourceCost.work (iterate 11 H) 3 3 6+2
def assemblyHeight (H K : ℕ) : ℕ := iterate 32 (PlayerSpecificAlgebraicNestedRemainingSizes.base H K)
def work (H K : ℕ) : ℕ := residualWork H+(PlayerSpecificCompareSourceCost.coefficient*(H+1)^3+2)+
  (PlayerSpecificNestedProfileSourceCost.work H K+PlayerSpecificDescriptorBinarySourceCost.work (assemblyHeight H K) 3 9 9)+
  PlayerSpecificDescriptorPadSourceCost.work (assemblyHeight H K) 3 9 9+2
theorem positive_profile (R C F P : ℕ) : R+C+F+2≤R+C+F+P+2 := by omega
theorem zero_profile (R C F P : ℕ) : R+C+P+2≤R+C+F+P+2 := by omega

theorem residual_cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedThirdProfileExecution.residual RationalCostModel.schoolbook root a).2≤residualWork H := by
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 11 H
  have ht:=PlayerSpecificResidualTableSourceCost.cost root a H hm hm0 hml hmH he hv hH ha
  have hd:=PlayerSpecificAlgebraicResidualTable.bounds RationalCostModel.schoolbook root a H ha hm hm0 hml hmH hH
  have hp:=PlayerSpecificDescriptorPadSourceCost.cost root (PlayerSpecificAlgebraicResidualTable.prepare RationalCostModel.schoolbook root a)
    6 0 (iterate 11 H) hm0 hml (mono hmH hbase) (mono he hbase) hd
  rw [PlayerSpecificNestedThirdProfileExecution.residual_price]
  exact Nat.add_le_add_right (Nat.add_le_add ht hp) 2

theorem cost (root : Candidate) (a : Input) (p : Prepared) (H K : ℕ) (outer : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p H) :
    (PlayerSpecificNestedThirdProfileExecution.run RationalCostModel.schoolbook root a p K outer).2≤work H K := by
  let model:=RationalCostModel.schoolbook
  let r:=PlayerSpecificAlgebraicNestedThirdProfile.residual model root a
  let f:=PlayerSpecificAlgebraicNestedFamily.profile model root a p.v K outer
  let U:=assemblyHeight H K
  have hHU : H≤U := PlayerSpecificAlgebraicNestedRemainingSizes.core_le 0 H K (by omega)
  have hru : iterate 11 H≤U := PlayerSpecificAlgebraicNestedRemainingSizes.core_le 11 H K (by omega)
  have hrb : Bounds root r U := by
    have ht:=PlayerSpecificAlgebraicResidualTable.bounds model root a H ha hm hm0 hml hmH hH
    have hpad:=PlayerSpecificAlgebraicDescriptorPad.bounds root _ 6 0 (iterate 11 H) hm0 ht
    exact PlayerSpecificSegmentDrawReturnSizes.bounds_mono root r (iterate 11 H) U hru hpad
  have hfb : Bounds root f U := PlayerSpecificAlgebraicNestedFamily.profile_bounds model root a p.v H ha hp.v hm hm0 hml hmH hH K outer
  have hr:=residual_cost root a H hm hm0 hml hmH he hv hH ha
  have hc : (PlayerSpecificNestedThirdProfileExecution.positive model root p).2≤PlayerSpecificCompareSourceCost.coefficient*(H+1)^3+2 := by
    rw [PlayerSpecificNestedThirdProfileExecution.positive_price]
    exact Nat.add_le_add_right (PlayerSpecificCompareSourceCost.cost root p.v [] H hm hm0 hml hmH he hv (by omega) hp.v
      ⟨nil_reduced _ hm0,nil_height _⟩) 2
  have hf:=PlayerSpecificNestedProfileSourceCost.cost root a p.v H K outer hm hm0 hml hmH he hv hH ha hp.v
  have hb:=PlayerSpecificDescriptorBinarySourceCost.cost root p.thirdAlpha f r U hm hm0 hml (mono hmH hHU) (mono he hHU) hv
    ((show 1≤H by omega).trans hHU) ⟨hp.thirdAlpha.1,mono hp.thirdAlpha.2 hHU⟩ hfb hrb
  have hpad:=PlayerSpecificDescriptorPadSourceCost.cost root r 9 0 U hm0 hml (mono hmH hHU) (mono he hHU) hrb
  simp only [PlayerSpecificNestedThirdProfileExecution.run,PlayerSpecificNestedThirdProfileExecution.packing,
    PlayerSpecificNestedThirdProfileExecution.residual_value,PlayerSpecificNestedProfileExecution.value]
  split
  · exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hr hc) (Nat.add_le_add hf hb)) 2).trans (positive_profile _ _ _ _)
  · exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hr hc) hpad) 2).trans (zero_profile _ _ _ _)

end Blotto.PlayerSpecificNestedThirdProfileSourceCost
