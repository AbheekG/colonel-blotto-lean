import Blotto.PlayerSpecificNestedSortedProfileExecution

/-! Complete sort/profile/restoration source work uses original raw
row height and midpoint precision. Sorting preserves every row size. -/
namespace Blotto.PlayerSpecificNestedSortedProfileSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def inputWork (H : ℕ) : ℕ := PlayerSpecificCompareSourceCost.coefficient*(H+1)^3+
  (3000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(H+11)^3+14
def work (H K : ℕ) : ℕ := inputWork H+PlayerSpecificNestedInteriorProfileSourceCost.work H K+
  PlayerSpecificDescriptorSwapSourceCost.work (PlayerSpecificAlgebraicNestedInteriorSizes.height H K) 18+2
theorem skip_profile (I P S : ℕ) : I+P+2≤I+P+S+2 := by omega

theorem input_cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedSortedProfileExecution.input RationalCostModel.schoolbook root a).2 ≤ inputWork H := by
  let model:=RationalCostModel.schoolbook
  let raw:=PlayerSpecificAlgebraicNestedSpecInput.sorted a (PlayerSpecificAlgebraicPairStep.le model root a.first a.second)
  let S:=H+10
  have hHS : H≤S := by dsimp [S]; omega
  have hr:=PlayerSpecificAlgebraicNestedSpecInputSizes.sorted_fits root a (PlayerSpecificAlgebraicPairStep.le model root a.first a.second) H ha
  have henv:=environment_bounds root a [] H ha ⟨nil_reduced _ hm0,nil_height _⟩
  have hout:=environment_bounds root raw [] H hr ⟨nil_reduced _ hm0,nil_height _⟩
  have hc:=PlayerSpecificCompareSourceCost.cost root a.first a.second H hm hm0 hml hmH he hv (by omega) ha.first ha.second
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root (environment a []) (environment raw []) S
    (mono hmH hHS) hml (mono he hHS)
    (fun j => ⟨mono (henv j).2 hHS,by have h:=(henv j).1.2; omega⟩)
    (fun j => ⟨mono (hout j).2 hHS,by have h:=(hout j).1.2; omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 3000 S)
  rw [show S+1=H+11 by rfl] at hf'
  rw [PlayerSpecificNestedSortedProfileExecution.input_price]
  exact Nat.add_le_add_right (Nat.add_le_add hc hf') 14

theorem cost (root : Candidate) (a : Input) (H K : ℕ) (outer : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedSortedProfileExecution.run RationalCostModel.schoolbook root a K outer).2≤work H K := by
  let model:=RationalCostModel.schoolbook
  let ordered:=PlayerSpecificAlgebraicPairStep.le model root a.first a.second
  let raw:=PlayerSpecificAlgebraicNestedSpecInput.sorted a ordered
  let U:=PlayerSpecificAlgebraicNestedInteriorSizes.height H K
  have hHU:=PlayerSpecificAlgebraicNestedInteriorSizes.input_le H K
  have hr:=PlayerSpecificAlgebraicNestedSpecInputSizes.sorted_fits root a ordered H ha
  have hi:=input_cost root a H hm hm0 hml hmH he hv hH ha
  have hp:=PlayerSpecificNestedInteriorProfileSourceCost.cost root raw H K outer hm hm0 hml hmH he hv hH hr
  have hd : PlayerSpecificAlgebraicDescriptorBounds.Bounds root (PlayerSpecificNestedInteriorProfileExecution.run model root raw K outer).1 U := by
    rw [PlayerSpecificNestedInteriorProfileExecution.value]
    exact PlayerSpecificAlgebraicNestedInteriorSizes.bounds model root raw H hr hm hm0 hml hmH hH K outer
  have hs:=PlayerSpecificDescriptorSwapSourceCost.cost root (PlayerSpecificNestedInteriorProfileExecution.run model root raw K outer).1 U hml
    (mono hmH hHU) (mono he hHU) hd
  simp only [PlayerSpecificNestedSortedProfileExecution.run,PlayerSpecificNestedSortedProfileExecution.input_value,PlayerSpecificNestedSortedProfileExecution.packing]
  split
  · exact (Nat.add_le_add_right (Nat.add_le_add hi hp) 2).trans (skip_profile _ _ _)
  · exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hi hp) hs) 2

end Blotto.PlayerSpecificNestedSortedProfileSourceCost
