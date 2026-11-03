import Blotto.PlayerSpecificThreePositiveExecution

/-! Complete source price for the actual positive-geometry test.
Its combined-total height is derived additively from raw input rows. -/
namespace Blotto.PlayerSpecificThreePositiveSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := PlayerSpecificAlgebraicGroupingEntryCost.polynomialCoefficient*11^3

theorem profile (A S R : ℕ) : 200000000*R+A*(S+1)*R+1400*R≤(A+200002000)*(S+1)*R := by
  nlinarith only [Nat.zero_le (S*R),Nat.zero_le R]

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root a H) :
    (PlayerSpecificThreePositiveExecution.run RationalCostModel.schoolbook root a).2≤coefficient*(H+1)^3 := by
  let S:=2*H+10
  let model:=RationalCostModel.schoolbook
  let combined:=PlayerSpecificFieldCombination.run false root.polynomial a.first a.second
  have hHS : H≤S := by dsimp [S]; omega
  have hsumRed : Reduced root.polynomial combined.1 := PlayerSpecificFieldCombination.reduced false _ _ _ hm hm0
  have hsumH : HasHeight combined.1 (2*H+1) := by
    change HasHeight (PlayerSpecificFieldCombination.run false root.polynomial a.first a.second).1 _
    rw [PlayerSpecificFieldCombination.value]
    change HasHeight (PlayerSpecificAlgebraicField.plus root.polynomial a.first a.second) _
    simpa only [two_mul] using PlayerSpecificShortReduction.plus_height _ _ _ hm hm0 ha.first.1 ha.second.1 H H ha.first.2 ha.second.2
  have hsumS:=PlayerSpecificPolynomialHeights.mono hsumH (show 2*H+1≤S by dsimp [S]; omega)
  have hal : a.first.length≤3 := by have h:=ha.first.1.2; omega
  have hbl : a.second.length≤3 := by have h:=ha.second.1.2; omega
  have hbudgetl : a.budget.length≤3 := by have h:=ha.budget.1.2; omega
  have hsuml : combined.1.length≤3 := by have h:=hsumRed.2; omega
  have hcomb:=(PlayerSpecificFieldCombinationCost.run_cost model false root.polynomial a.first a.second hm hm0 hml S
    (mono hmH hHS) (mono ha.first.2 hHS) (mono ha.second.2 hHS) (by dsimp [S]; omega) hal hbl).trans
      (Nat.mul_le_mul_left _ (model.monotone (PlayerSpecificAlgebraicExpressionPrimitiveCost.combination_width S)))
  have hcmp:=PlayerSpecificAlgebraicComparisonExecution.cost model root combined.1 a.budget S hm hm0 hml
    (mono hmH hHS) (mono he hHS) hv hsumS (mono ha.budget.2 hHS) hsuml hbudgetl (by dsimp [S]; omega)
  have hraw:=PlayerSpecificThreePreparationInputs.raw (PlayerSpecificThreePreparationInputs.mono root a H S ha hHS)
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root (PlayerSpecificThreeEnvironmentExecution.input a)
    (FixedArrayTable.ofFn (fun _ : Fin 1 => combined.1)) S (mono hmH hHS) hml (mono he hHS)
    (fun j => ⟨(hraw j).2,by have h:=(hraw j).1.2; omega⟩)
    (by intro j; rw [FixedArrayTable.read_ofFn]; exact ⟨hsumS,hsuml⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hsum:=Nat.add_le_add (Nat.add_le_add hcomb hcmp) hf
  have hc : (PlayerSpecificThreePositiveExecution.run model root a).2≤PlayerSpecificAlgebraicGroupingSourceCost.work model S :=
    hsum.trans (profile PlayerSpecificAlgebraicComparisonExecution.coefficient S _)
  have hp : PlayerSpecificAlgebraicGroupingSourceCost.work model S≤PlayerSpecificAlgebraicGroupingEntryCost.polynomialCoefficient*(S+1)^3 := by
    unfold PlayerSpecificAlgebraicGroupingSourceCost.work
    rw [PlayerSpecificAlgebraicComparisonCost.width_linear]
    exact PlayerSpecificAlgebraicPairCost.cubic_profile PlayerSpecificAlgebraicGroupingSourceCost.coefficient
      PlayerSpecificAlgebraicComparisonCost.widthCoefficient (S+1) (by omega)
  exact (hc.trans hp).trans (PlayerSpecificThreePreparationInputs.transfer _ 11 H (S+1) (by dsimp [S]; omega))

end Blotto.PlayerSpecificThreePositiveSourceCost
