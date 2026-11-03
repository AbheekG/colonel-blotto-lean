import Blotto.PlayerSpecificUnorderedThreeExecution

/-! Complete source work of the actual unsorted three-variable table:
comparison, one ordered continuation, coordinate restoration and return. -/
namespace Blotto.PlayerSpecificUnorderedThreeSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := PlayerSpecificAlgebraicComparisonCost.comparisonCoefficient+PlayerSpecificOrderedThreeSourceCost.coefficient+
  PlayerSpecificThreePreparationInputs.frameCoefficient+12

theorem profile (U V W X : ℕ) (hX : 1≤X) : U*X+V*X+W*X+12≤(U+V+W+12)*X := by
  nlinarith only [hX]

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root a H) :
    (PlayerSpecificUnorderedThreeExecution.run RationalCostModel.schoolbook root a).2≤coefficient*(H+1)^3 := by
  let model:=RationalCostModel.schoolbook
  let compared:=PlayerSpecificAlgebraicComparisonExecution.run model root a.first a.second
  let result:=PlayerSpecificUnorderedThreeExecution.selected model root a compared.1
  have hal : a.first.length≤3 := by have h:=ha.first.1.2; omega
  have hbl : a.second.length≤3 := by have h:=ha.second.1.2; omega
  have hc:=PlayerSpecificAlgebraicComparisonCost.comparison root a.first a.second H hm hm0 hml hmH he hv ha.first.2 ha.second.2 hal hbl (by omega)
  have hs : result.2≤PlayerSpecificOrderedThreeSourceCost.coefficient*(H+1)^3 := by
    dsimp only [result,PlayerSpecificUnorderedThreeExecution.selected]
    split
    · exact PlayerSpecificOrderedThreeSourceCost.cost root a H hm hm0 hml hmH he hv hH ha
    · exact PlayerSpecificOrderedThreeSourceCost.cost root (PlayerSpecificAlgebraicUnorderedThree.swapped a) H hm hm0 hml hmH he hv hH
        (PlayerSpecificAlgebraicThreeEnvironmentSizes.swapped root a H ha)
  have hd : PlayerSpecificAlgebraicDescriptorBounds.Bounds root (PlayerSpecificUnorderedThreeExecution.run model root a).1
      (PlayerSpecificAlgebraicHeightEnvelope.iterate 20 H) := by
    rw [PlayerSpecificUnorderedThreeExecution.value]
    exact PlayerSpecificAlgebraicThreeDescriptorSizes.unordered model root a H ha hm hm0 hml hmH hH
  have hf:=PlayerSpecificThreePreparationInputs.frame_polynomial root a
    (PlayerSpecificUnorderedThreeExecution.run model root a).1 H hmH hml he ha hd
  have hsum:=Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc hs) hf) 12
  change _≤coefficient*(H+1)^3
  change _+PlayerSpecificRationalTrace.price model (List.replicate 6 (.control 1))≤_
  rw [PlayerSpecificUnorderedThreeExecution.packing]
  exact hsum.trans (profile _ _ _ _ (Nat.succ_le_of_lt (pow_pos (by omega : 0<H+1) 3)))

theorem same_return_and_cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root a H) :
    (PlayerSpecificUnorderedThreeExecution.run RationalCostModel.schoolbook root a).1=
      PlayerSpecificAlgebraicUnorderedThree.prepare RationalCostModel.schoolbook root a ∧
    (PlayerSpecificUnorderedThreeExecution.run RationalCostModel.schoolbook root a).2≤coefficient*(H+1)^3 :=
  ⟨PlayerSpecificUnorderedThreeExecution.value _ root a,cost root a H hm hm0 hml hmH he hv hH ha⟩

end Blotto.PlayerSpecificUnorderedThreeSourceCost
