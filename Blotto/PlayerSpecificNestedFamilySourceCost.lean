import Blotto.PlayerSpecificNestedFamilyExecution

/-! Complete conditional family source work with actual output sizes
derived from its original input and reached short-length row. -/
namespace Blotto.PlayerSpecificNestedFamilySourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := PlayerSpecificNestedParameterSourceCost.scalarCoefficient*(H+19)^3+
  (3000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 9 H+11)^3+12

theorem cost (root : Candidate) (a : Input) (short : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hShort : Reduced root.polynomial short ∧ HasHeight short H) :
    (PlayerSpecificNestedFamilyExecution.run RationalCostModel.schoolbook root a short).2≤work H := by
  let model:=RationalCostModel.schoolbook
  let result:=(PlayerSpecificNestedFamilyExecution.run model root a short).1
  let S:=iterate 9 H+10
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 9 H
  have hHS : H≤S := by dsimp [S]; omega
  have hout : Fits root result (iterate 9 H) := by
    change Fits root (PlayerSpecificNestedFamilyExecution.run model root a short).1 (iterate 9 H)
    rw [PlayerSpecificNestedFamilyExecution.value]
    exact PlayerSpecificAlgebraicNestedFamily.fits model root a short H ha hShort hm hm0 hml hmH hH
  have henv:=environment_bounds root a short H ha hShort
  have hresult:=environment_bounds root result [] (iterate 9 H) hout ⟨nil_reduced _ hm0,nil_height _⟩
  have hs:=PlayerSpecificNestedParameterSourceCost.scalar_cost root a short 2 H hm hm0 hml hmH he hv hH ha hShort
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root (environment a short) (environment result []) S
    (mono hmH hHS) hml (mono he hHS)
    (fun j => ⟨mono (henv j).2 hHS,by have h:=(henv j).1.2; omega⟩)
    (fun j => ⟨mono (hresult j).2 (by dsimp [S]; omega),by have h:=(hresult j).1.2; omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 3000 S)
  rw [show S+1=iterate 9 H+11 by rfl] at hf'
  rw [PlayerSpecificNestedFamilyExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add hs hf') 12

end Blotto.PlayerSpecificNestedFamilySourceCost
