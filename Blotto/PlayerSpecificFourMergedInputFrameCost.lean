import Blotto.PlayerSpecificFourMergedInputExecution

/-! The complete scaled-input return frame has original-input-derived
sizes for both split lengths and all five child fields. -/
namespace Blotto.PlayerSpecificFourMergedInputFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hH : 2≤H) (ha : Fits root a H) :
    price RationalCostModel.schoolbook (PlayerSpecificExpressionVectorExecution.frame root (environment a)
      (PlayerSpecificFourMergedInputExecution.fields (PlayerSpecificFourMergedInputExecution.run RationalCostModel.schoolbook root a).1))≤
        (2800*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 15 H+11)^3 := by
  let model:=RationalCostModel.schoolbook
  let result:=(PlayerSpecificFourMergedInputExecution.run model root a).1
  let S:=iterate 15 H+10
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 15 H
  have hHS : H≤S := by dsimp [S]; omega
  have hout : (Reduced root.polynomial result.first ∧ HasHeight result.first (iterate 15 H)) ∧
      (Reduced root.polynomial result.second ∧ HasHeight result.second (iterate 15 H)) ∧
      PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root result.child (iterate 15 H) := by
    dsimp only [result]
    rw [PlayerSpecificFourMergedInputExecution.value]
    exact PlayerSpecificAlgebraicFourMergedSizes.bounds model root a H ha hm hm0 hml hmH hH
  have hfields : ∀ j,Reduced root.polynomial ((PlayerSpecificFourMergedInputExecution.fields result).read j) ∧
      HasHeight ((PlayerSpecificFourMergedInputExecution.fields result).read j) (iterate 15 H) := by
    intro j
    fin_cases j
    · simpa [PlayerSpecificFourMergedInputExecution.fields,FixedArrayTable.read_ofFn] using hout.1
    · simpa [PlayerSpecificFourMergedInputExecution.fields,FixedArrayTable.read_ofFn] using hout.2.1
    · simpa [PlayerSpecificFourMergedInputExecution.fields,FixedArrayTable.read_ofFn] using hout.2.2.budget
    · simpa [PlayerSpecificFourMergedInputExecution.fields,FixedArrayTable.read_ofFn] using hout.2.2.first
    · simpa [PlayerSpecificFourMergedInputExecution.fields,FixedArrayTable.read_ofFn] using hout.2.2.second
    · simpa [PlayerSpecificFourMergedInputExecution.fields,FixedArrayTable.read_ofFn] using hout.2.2.third
    · simpa [PlayerSpecificFourMergedInputExecution.fields,FixedArrayTable.read_ofFn] using hout.2.2.probability
  have henv:=environment_bounds root a H ha
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root (environment a) (PlayerSpecificFourMergedInputExecution.fields result) S
    (mono hmH hHS) hml (mono he hHS)
    (fun j => ⟨mono (henv j).2 hHS,by have h:=(henv j).1.2; omega⟩)
    (fun j => ⟨mono (hfields j).2 (by dsimp [S]; omega),by have h:=(hfields j).1.2; omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 2800 S)
  rw [show S+1=iterate 15 H+11 by rfl] at hf'
  exact hf'

end Blotto.PlayerSpecificFourMergedInputFrameCost
