import Blotto.PlayerSpecificNestedRestoreExecution

/-! Fixed-focus allocation restoration preserves row heights and has
a complete cubic original-row-height source price. -/
namespace Blotto.PlayerSpecificNestedRestoreSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicReduction
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := (1400*PlayerSpecificResourceCostProfile.rationalCoefficient)*(H+6)^3+28

theorem cost (root : Candidate) (focus : Fin 3) (a : FixedArrayTable 3 Data) (H : ℕ)
    (hml : root.polynomial.length≤4) (hmH : HasHeight root.polynomial H)
    (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (ha : ∀ j,Reduced root.polynomial (a.read j) ∧ HasHeight (a.read j) H) :
    (PlayerSpecificNestedRestoreExecution.run RationalCostModel.schoolbook root focus a).2≤work H := by
  let model:=RationalCostModel.schoolbook
  let result:=(PlayerSpecificNestedRestoreExecution.run model root focus a).1
  let S:=H+5
  have hHS : H≤S := by dsimp [S]; omega
  have hout : ∀ j,Reduced root.polynomial (result.read j) ∧ HasHeight (result.read j) H := by
    intro j
    change Reduced root.polynomial ((PlayerSpecificNestedRestoreExecution.run model root focus a).1.read j) ∧
      HasHeight ((PlayerSpecificNestedRestoreExecution.run model root focus a).1.read j) H
    rw [PlayerSpecificNestedRestoreExecution.value,PlayerSpecificAlgebraicNestedTerminalDraw.restore,FixedArrayTable.read_ofFn]
    exact ha _
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root a result S (mono hmH hHS) hml (mono he hHS)
    (fun j => ⟨mono (ha j).2 hHS,by have h:=(ha j).1.2; omega⟩)
    (fun j => ⟨mono (hout j).2 hHS,by have h:=(hout j).1.2; omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 1400 S)
  rw [show S+1=H+6 by rfl] at hf'
  rw [PlayerSpecificNestedRestoreExecution.price_equation]
  exact Nat.add_le_add hf' (PlayerSpecificNestedRestoreExecution.packing_cost model focus)

end Blotto.PlayerSpecificNestedRestoreSourceCost
