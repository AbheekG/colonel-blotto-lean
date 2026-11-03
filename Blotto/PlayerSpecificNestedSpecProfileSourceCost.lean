import Blotto.PlayerSpecificNestedSpecProfileExecution

/-! Complete closed-probability profile source work derives every
constant and reached endpoint/interior size from original raw rows. -/
namespace Blotto.PlayerSpecificNestedSpecProfileSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def qOneWork (H : ℕ) : ℕ := (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(H+1)^3+
  PlayerSpecificCompareSourceCost.coefficient*(step H+1)^3+2
def work (H K : ℕ) : ℕ := PlayerSpecificCompareSourceCost.coefficient*(H+1)^3+qOneWork H+
  PlayerSpecificNestedEndpointProfileSourceCost.work H+PlayerSpecificNestedEndpointProfileSourceCost.work H+
  PlayerSpecificNestedSortedProfileSourceCost.work H K+4
theorem zero_profile (C O E S : ℕ) : C+E+2≤C+O+E+E+S+4 := by omega
theorem one_profile (C O E S : ℕ) : C+O+E+4≤C+O+E+E+S+4 := by omega
theorem interior_profile (C O E S : ℕ) : C+O+S+4≤C+O+E+E+S+4 := by omega

theorem qOne_cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedSpecProfileExecution.qOne RationalCostModel.schoolbook root a).2≤qOneWork H := by
  let model:=RationalCostModel.schoolbook
  let one:=PlayerSpecificAlgebraicField.constant root.polynomial 1
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 1 H
  have hone : Reduced root.polynomial one ∧ HasHeight one (step H) :=
    ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,constant_height root.polynomial 1 H hmH (one_height.mono (by omega)) (by omega) hml⟩
  have hc:=(PlayerSpecificAlgebraicExpressionPrimitiveCost.constant_cost model root 1 H hm hm0 hml hmH (one_height.mono (by omega))
    (by omega)).trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 H)
  have ht:=PlayerSpecificCompareSourceCost.cost root one a.probability (step H) hm hm0 hml (mono hmH hbase) (mono he hbase) hv
    ((show 1≤H by omega).trans hbase) hone ⟨ha.probability.1,mono ha.probability.2 hbase⟩
  rw [PlayerSpecificNestedSpecProfileExecution.qOne_price]
  exact Nat.add_le_add_right (Nat.add_le_add hc ht) 2

theorem cost (root : Candidate) (a : Input) (H K : ℕ) (outer : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedSpecProfileExecution.run RationalCostModel.schoolbook root a K outer).2≤work H K := by
  have hz:=PlayerSpecificCompareSourceCost.cost root a.probability [] H hm hm0 hml hmH he hv (by omega) ha.probability ⟨nil_reduced _ hm0,nil_height _⟩
  have ho:=qOne_cost root a H hm hm0 hml hmH he hv hH ha
  have he0:=PlayerSpecificNestedEndpointProfileSourceCost.cost root a false H hm hm0 hml hmH he hv hH ha
  have he1:=PlayerSpecificNestedEndpointProfileSourceCost.cost root a true H hm hm0 hml hmH he hv hH ha
  have hi:=PlayerSpecificNestedSortedProfileSourceCost.cost root a H K outer hm hm0 hml hmH he hv hH ha
  simp only [PlayerSpecificNestedSpecProfileExecution.run,PlayerSpecificNestedSpecProfileExecution.packing,
    PlayerSpecificNestedSpecProfileExecution.two_tests_packing]
  split
  · exact (Nat.add_le_add_right (Nat.add_le_add hz he0) 2).trans (zero_profile _ _ _ _)
  · split
    · exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hz ho) he1) 4).trans (one_profile _ _ _ _)
    · exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hz ho) hi) 4).trans (interior_profile _ _ _ _)

end Blotto.PlayerSpecificNestedSpecProfileSourceCost
