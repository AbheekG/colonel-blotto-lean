import Blotto.PlayerSpecificFourReflectedInputExecution

/-! The reflected resource record charges every original and returned
field, including both stored copies of each initial amount. -/
namespace Blotto.PlayerSpecificFourReflectedInputFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H : ℕ)
    (hm : Normalized r.root.polynomial) (hm0 : r.root.polynomial≠[]) (hml : r.root.polynomial.length≤4)
    (hmH : HasHeight r.root.polynomial H) (he : HasHeight [r.root.interval.lo,r.root.interval.hi] H)
    (hH : 2≤H) (ha : Fits r.root a H) :
    price RationalCostModel.schoolbook (PlayerSpecificExpressionVectorExecution.frame r.root (environment a)
      (PlayerSpecificFourReflectedInputExecution.fields
        (PlayerSpecificFourReflectedInputExecution.run RationalCostModel.schoolbook r a).1))≤
      (4600*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 15 H+21)^3 := by
  let model:=RationalCostModel.schoolbook
  let result:=(PlayerSpecificFourReflectedInputExecution.run model r a).1
  let S:=iterate 15 H+20
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 15 H
  have hHS : H≤S := by dsimp [S]; omega
  have hb : (∀ j,Reduced r.root.polynomial (result.long.read j) ∧
      HasHeight (result.long.read j) (iterate 15 H)) ∧
      (∀ j,Reduced r.root.polynomial (result.short.read j) ∧
      HasHeight (result.short.read j) (iterate 15 H)) ∧
      (∀ j,(Reduced r.root.polynomial (result.resources.rows.read j).length ∧
        HasHeight (result.resources.rows.read j).length (iterate 15 H)) ∧
        (Reduced r.root.polynomial (result.resources.rows.read j).initialA ∧
        HasHeight (result.resources.rows.read j).initialA (iterate 15 H))) ∧
      (Reduced r.root.polynomial result.budget ∧ HasHeight result.budget (iterate 15 H)) := by
    dsimp only [result]
    rw [PlayerSpecificFourReflectedInputExecution.value]
    exact PlayerSpecificAlgebraicFourReflectedSizes.bounds model r a H ha hm hm0 hml hmH hH
  have hcopy : ∀ j,(result.resources.rows.read j).initialB=(result.resources.rows.read j).initialA := by
    intro j
    dsimp only [result]
    rw [PlayerSpecificFourReflectedInputExecution.value]
    simp only [PlayerSpecificAlgebraicFourReflectedInput.prepare,FixedArrayTable.read_ofFn]
  have hfields : ∀ j,Reduced r.root.polynomial ((PlayerSpecificFourReflectedInputExecution.fields result).read j) ∧
      HasHeight ((PlayerSpecificFourReflectedInputExecution.fields result).read j) (iterate 15 H) := by
    intro j
    fin_cases j
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.1 0
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.1 1
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.1 2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.2.1 0
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.2.1 1
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.2.1 2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 0).1
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 1).1
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 2).1
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 0).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 1).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using (hb.2.2.1 2).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn,hcopy] using (hb.2.2.1 0).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn,hcopy] using (hb.2.2.1 1).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn,hcopy] using (hb.2.2.1 2).2
    · simpa [PlayerSpecificFourReflectedInputExecution.fields,FixedArrayTable.read_ofFn] using hb.2.2.2
  have henv:=environment_bounds r.root a H ha
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model r.root (environment a)
    (PlayerSpecificFourReflectedInputExecution.fields result) S
    (mono hmH hHS) hml (mono he hHS)
    (fun j => ⟨mono (henv j).2 hHS,by have h:=(henv j).1.2; omega⟩)
    (fun j => ⟨mono (hfields j).2 (by dsimp [S]; omega),by have h:=(hfields j).1.2; omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 4600 S)
  rw [show S+1=iterate 15 H+21 by rfl] at hf'
  exact hf'

end Blotto.PlayerSpecificFourReflectedInputFrameCost
