import Blotto.PlayerSpecificDescriptorSwapExecution

/-! The complete fixed swap has a polynomial source price in original
row height and slot count; it preserves the actual coefficient sizes. -/
namespace Blotto.PlayerSpecificDescriptorSwapSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicReduction
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H slots : ℕ) : ℕ := PlayerSpecificDescriptorCopySourceCost.coefficient*(H+slots+4)^5+
  PlayerSpecificDescriptorCopySourceCost.coefficient*(H+slots+4)^5+7

theorem cost {slots : ℕ} (root : Candidate) (d : Descriptor 3 slots) (H : ℕ)
    (hml : root.polynomial.length≤4) (hmH : HasHeight root.polynomial H)
    (he : HasHeight [root.interval.lo,root.interval.hi] H) (hd : Bounds root d H) :
    (PlayerSpecificDescriptorSwapExecution.run RationalCostModel.schoolbook root d).2≤work H slots := by
  let env:=PlayerSpecificDescriptorPadExecution.environment
  have henv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H := fun j => Fin.elim0 j
  have hi:=PlayerSpecificDescriptorCopySourceCost.cost root env d H hmH hml he henv hd
  have ho:=PlayerSpecificDescriptorCopySourceCost.cost root env (PlayerSpecificAlgebraicDescriptorSwap.swap d) H hmH hml he henv
    (PlayerSpecificAlgebraicDescriptorSwap.bounds root d H hd)
  rw [show H+3+slots+0+1=H+slots+4 by omega] at hi ho
  change _+price RationalCostModel.schoolbook (PlayerSpecificAlgebraicCallerFrame.run [] [1,0,2])≤_
  rw [PlayerSpecificDescriptorSwapExecution.packing]
  exact Nat.add_le_add_right (Nat.add_le_add hi ho) 7

end Blotto.PlayerSpecificDescriptorSwapSourceCost
