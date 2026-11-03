import Blotto.PlayerSpecificNestedCaseParameterExecution

/-! Complete cached nested case parameters have a polynomial source
price in the six raw input row heights, with all return sizes derived. -/
namespace Blotto.PlayerSpecificNestedCaseParameterSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frameCoefficient : ℕ := (2800*PlayerSpecificResourceCostProfile.rationalCoefficient)*
  ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^9+11)^3
def coefficient : ℕ := PlayerSpecificResidualEnvironmentSourceCost.coefficient*23^3+
  3*(PlayerSpecificNestedParameterSourceCost.scalarCoefficient*19^3)+frameCoefficient+20

theorem frame_cost (root : Candidate) (a : Input) (H : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hH : 2≤H) (ha : Fits root a H) :
    price RationalCostModel.schoolbook (PlayerSpecificNestedCaseParameterExecution.frame root a
      (PlayerSpecificNestedCaseParameterExecution.run RationalCostModel.schoolbook root a).1)≤frameCoefficient*(H+1)^3 := by
  let model:=RationalCostModel.schoolbook
  let p:=(PlayerSpecificNestedCaseParameterExecution.run model root a).1
  let T:=PlayerSpecificAlgebraicHeightEnvelope.iterate 9 H
  let U:=T+10
  have hbase : H≤T := PlayerSpecificAlgebraicExpressionBudget.initial_le 9 H
  have hHU : H≤U := by dsimp [U]; omega
  have hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p T := by
    change PlayerSpecificAlgebraicNestedCaseParameters.Bounds root (PlayerSpecificNestedCaseParameterExecution.run model root a).1 T
    rw [PlayerSpecificNestedCaseParameterExecution.value]
    exact PlayerSpecificAlgebraicNestedCaseParameters.bounds model root a H ha hm hm0 hml hmH hH
  have hfields : ∀ j,HasHeight ((PlayerSpecificNestedCaseParameterExecution.fields p).read j) U ∧
      ((PlayerSpecificNestedCaseParameterExecution.fields p).read j).length≤3 := by
    have hout : ∀ row : Data,Reduced root.polynomial row ∧ HasHeight row T → HasHeight row U ∧ row.length≤3 := by
      intro row hr
      exact ⟨mono hr.2 (by dsimp [U]; omega),by have h:=hr.1.2; omega⟩
    intro j
    fin_cases j
    · simpa [PlayerSpecificNestedCaseParameterExecution.fields,FixedArrayTable.read_ofFn] using hout p.u hp.u
    · simpa [PlayerSpecificNestedCaseParameterExecution.fields,FixedArrayTable.read_ofFn] using hout p.v hp.v
    · simpa [PlayerSpecificNestedCaseParameterExecution.fields,FixedArrayTable.read_ofFn] using hout p.h hp.h
    · simpa [PlayerSpecificNestedCaseParameterExecution.fields,FixedArrayTable.read_ofFn] using hout p.mirror hp.mirror
    · simpa [PlayerSpecificNestedCaseParameterExecution.fields,FixedArrayTable.read_ofFn] using hout p.secondAlpha hp.secondAlpha
    · simpa [PlayerSpecificNestedCaseParameterExecution.fields,FixedArrayTable.read_ofFn] using hout p.thirdAlpha hp.thirdAlpha
  have henv:=environment_bounds root a [] H ha ⟨nil_reduced _ hm0,nil_height _⟩
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root (environment a []) (PlayerSpecificNestedCaseParameterExecution.fields p) U
    (mono hmH hHU) hml (mono he hHU) (fun j => ⟨mono (henv j).2 hHU,by have h:=(henv j).1.2; omega⟩) hfields
    (by dsimp [U]; omega) (by dsimp [U]; omega) (by dsimp [U]; omega)
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 2800 U)
  exact hf'.trans (PlayerSpecificThreePreparationInputs.transfer _ _ H (U+1) (PlayerSpecificThreePreparationInputs.shift 9 H 11))

theorem profile (G C F X : ℕ) (hX : 1≤X) : G*X+C*X+C*X+C*X+F*X+20≤(G+3*C+F+20)*X := by nlinarith only [hX]

theorem cost (root : Candidate) (a : Input) (H : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedCaseParameterExecution.run RationalCostModel.schoolbook root a).2≤coefficient*(H+1)^3 := by
  let model:=RationalCostModel.schoolbook
  have hg:=(PlayerSpecificResidualEnvironmentSourceCost.cost root a H hm hm0 hml hmH he hv ha).trans
    (PlayerSpecificThreePreparationInputs.transfer _ 23 H (H+23) (by omega))
  have hscalar : ∀ j : Fin 6,(PlayerSpecificNestedParameterExecution.scalar model root a [] j).2≤
      (PlayerSpecificNestedParameterSourceCost.scalarCoefficient*19^3)*(H+1)^3 := fun j =>
    (PlayerSpecificNestedParameterSourceCost.scalar_cost root a [] j H hm hm0 hml hmH he hv hH ha ⟨nil_reduced _ hm0,nil_height _⟩).trans
      (PlayerSpecificThreePreparationInputs.transfer _ 19 H (H+19) (by omega))
  have hf:=frame_cost root a H hm hm0 hml hmH he hH ha
  have hsum:=Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hg (hscalar 3)) (hscalar 4)) (hscalar 5)) hf) 20
  change _+price model (List.replicate 10 (.control 1))≤_
  rw [PlayerSpecificNestedCaseParameterExecution.packing]
  exact hsum.trans (profile _ _ _ _ (Nat.succ_le_of_lt (pow_pos (by omega : 0<H+1) 3)))

end Blotto.PlayerSpecificNestedCaseParameterSourceCost
