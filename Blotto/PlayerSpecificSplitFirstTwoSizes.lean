import Blotto.PlayerSpecificSplitFirstTwoExecution

/-! Split temporaries and returned rows have sizes derived from the
original split lengths and reached three-coordinate allocation. -/
namespace Blotto.PlayerSpecificSplitFirstTwoSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem fractions (root : Candidate) (a d : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (hH : 1≤H)
    (ha : Reduced root.polynomial a ∧ HasHeight a H) (hd : Reduced root.polynomial d ∧ HasHeight d H) :
    (Reduced root.polynomial (PlayerSpecificAlgebraicField.plus root.polynomial a d) ∧
      HasHeight (PlayerSpecificAlgebraicField.plus root.polynomial a d) (step H)) ∧
    (∀ z,Reduced root.polynomial z ∧ HasHeight z H →
      Reduced root.polynomial (PlayerSpecificAlgebraicField.divide root.polynomial z (PlayerSpecificAlgebraicField.plus root.polynomial a d)) ∧
        HasHeight (PlayerSpecificAlgebraicField.divide root.polynomial z (PlayerSpecificAlgebraicField.plus root.polynomial a d)) (iterate 2 H)) := by
  have hbase : H≤step H := (Nat.le_succ _).trans (large H)
  have hsumR:=PlayerSpecificAlgebraicField.plus_reduced root.polynomial a d hm hm0
  have hsumH:=(PlayerSpecificAlgebraicExpressionBudget.binary_heights RationalCostModel.schoolbook root a d H hm hm0 hml ha.1 hd.1 hmH ha.2 hd.2 hH).1
  refine ⟨⟨hsumR,hsumH⟩,?_⟩
  intro z hz
  exact ⟨PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0,
    divide_height root.polynomial z _ (step H) hm hm0 hml hz.1 hsumR (mono hmH hbase) (mono hz.2 hbase) hsumH (hH.trans hbase)⟩

theorem frame_cost (root : Candidate) (a d : Data) (y : FixedArrayTable 3 Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H) (hH : 1≤H)
    (ha : Reduced root.polynomial a ∧ HasHeight a H) (hd : Reduced root.polynomial d ∧ HasHeight d H)
    (hy : ∀ j,Reduced root.polynomial (y.read j) ∧ HasHeight (y.read j) H) :
    price RationalCostModel.schoolbook (PlayerSpecificExpressionVectorExecution.frame root (PlayerSpecificSplitFirstTwoExecution.environment a d y)
      (PlayerSpecificSplitFirstTwoExecution.run RationalCostModel.schoolbook root a d y).1)≤
        (2000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 3 H+11)^3 := by
  let model:=RationalCostModel.schoolbook
  let S:=iterate 3 H+10
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 3 H
  have hHS : H≤S := by dsimp [S]; omega
  have henv : ∀ j,Reduced root.polynomial ((PlayerSpecificSplitFirstTwoExecution.environment a d y).read j) ∧
      HasHeight ((PlayerSpecificSplitFirstTwoExecution.environment a d y).read j) H := by
    intro j
    fin_cases j
    · simpa [PlayerSpecificSplitFirstTwoExecution.environment,FixedArrayTable.read_ofFn] using ha
    · simpa [PlayerSpecificSplitFirstTwoExecution.environment,FixedArrayTable.read_ofFn] using hd
    · simpa [PlayerSpecificSplitFirstTwoExecution.environment,FixedArrayTable.read_ofFn] using hy 0
    · simpa [PlayerSpecificSplitFirstTwoExecution.environment,FixedArrayTable.read_ofFn] using hy 1
    · simpa [PlayerSpecificSplitFirstTwoExecution.environment,FixedArrayTable.read_ofFn] using hy 2
  have hout : ∀ j,Reduced root.polynomial ((PlayerSpecificSplitFirstTwoExecution.run model root a d y).1.read j) ∧
      HasHeight ((PlayerSpecificSplitFirstTwoExecution.run model root a d y).1.read j) (iterate 3 H) := by
    rw [PlayerSpecificSplitFirstTwoExecution.value]
    exact PlayerSpecificAlgebraicSplitFirstTwo.bounds root a d y H hm hm0 hml hmH hH ha hd hy
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root (PlayerSpecificSplitFirstTwoExecution.environment a d y)
    (PlayerSpecificSplitFirstTwoExecution.run model root a d y).1 S (mono hmH hHS) hml (mono he hHS)
    (fun j => ⟨mono (henv j).2 hHS,by have h:=(henv j).1.2; omega⟩)
    (fun j => ⟨mono (hout j).2 (by dsimp [S]; omega),by have h:=(hout j).1.2; omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 2000 S)
  rw [show S+1=iterate 3 H+11 by rfl] at hf'
  exact hf'

end Blotto.PlayerSpecificSplitFirstTwoSizes
