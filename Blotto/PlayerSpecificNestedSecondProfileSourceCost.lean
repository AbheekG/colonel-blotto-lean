import Blotto.PlayerSpecificNestedSecondProfileExecution

/-! Complete second profile source work, including the selected-only
uniform component, strict boundary comparison and mixture assembly. -/
namespace Blotto.PlayerSpecificNestedSecondProfileSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H K : ℕ) : ℕ := PlayerSpecificNestedProfileSourceCost.work H K+(PlayerSpecificCompareSourceCost.coefficient*(H+1)^3+2)+
  (PlayerSpecificNestedSecondUniformSourceCost.work H+
    PlayerSpecificDescriptorBinarySourceCost.work (PlayerSpecificNestedThirdProfileSourceCost.assemblyHeight H K) 3 9 9)+
  PlayerSpecificDescriptorPadSourceCost.work (PlayerSpecificNestedThirdProfileSourceCost.assemblyHeight H K) 3 9 9+2

theorem cost (root : Candidate) (a : Input) (p : Prepared) (H K : ℕ) (outer : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p H) :
    (PlayerSpecificNestedSecondProfileExecution.run RationalCostModel.schoolbook root a p K outer).2≤work H K := by
  let model:=RationalCostModel.schoolbook
  let f:=PlayerSpecificAlgebraicNestedFamily.profile model root a p.mirror K outer
  let uniform:=PlayerSpecificAlgebraicNestedSecondUniform.prepare model root a p
  let U:=PlayerSpecificNestedThirdProfileSourceCost.assemblyHeight H K
  have hHU : H≤U := PlayerSpecificAlgebraicNestedRemainingSizes.core_le 0 H K (by omega)
  have huu : iterate 22 H≤U := PlayerSpecificAlgebraicNestedRemainingSizes.core_le 22 H K (by omega)
  have hub : Bounds root uniform U := PlayerSpecificSegmentDrawReturnSizes.bounds_mono root uniform (iterate 22 H) U huu
    (PlayerSpecificAlgebraicNestedSecondSizes.bounds model root a p H ha hp hm hm0 hml hmH hH)
  have hfb : Bounds root f U := PlayerSpecificAlgebraicNestedFamily.profile_bounds model root a p.mirror H ha hp.mirror hm hm0 hml hmH hH K outer
  have hf:=PlayerSpecificNestedProfileSourceCost.cost root a p.mirror H K outer hm hm0 hml hmH he hv hH ha hp.mirror
  have hc : (PlayerSpecificNestedSecondProfileExecution.strict model root a p).2≤PlayerSpecificCompareSourceCost.coefficient*(H+1)^3+2 := by
    rw [PlayerSpecificNestedSecondProfileExecution.strict_price]
    exact Nat.add_le_add_right (PlayerSpecificCompareSourceCost.cost root a.short p.mirror H hm hm0 hml hmH he hv (by omega) ha.short hp.mirror) 2
  have hu:=PlayerSpecificNestedSecondUniformSourceCost.cost root a p H hm hm0 hml hmH he hv hH ha hp
  have hb:=PlayerSpecificDescriptorBinarySourceCost.cost root p.secondAlpha f uniform U hm hm0 hml (mono hmH hHU) (mono he hHU) hv
    ((show 1≤H by omega).trans hHU) ⟨hp.secondAlpha.1,mono hp.secondAlpha.2 hHU⟩ hfb hub
  have hpad:=PlayerSpecificDescriptorPadSourceCost.cost root f 9 0 U hm0 hml (mono hmH hHU) (mono he hHU) hfb
  simp only [PlayerSpecificNestedSecondProfileExecution.run,PlayerSpecificNestedSecondProfileExecution.packing,
    PlayerSpecificNestedProfileExecution.value,PlayerSpecificNestedSecondUniformExecution.value]
  split
  · exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hf hc) (Nat.add_le_add hu hb)) 2).trans
      (PlayerSpecificNestedThirdProfileSourceCost.positive_profile _ _ _ _)
  · exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hf hc) hpad) 2).trans
      (PlayerSpecificNestedThirdProfileSourceCost.zero_profile _ _ _ _)

end Blotto.PlayerSpecificNestedSecondProfileSourceCost
