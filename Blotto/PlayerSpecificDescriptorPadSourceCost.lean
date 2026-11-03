import Blotto.PlayerSpecificDescriptorPadExecution

/-! Complete padding has an explicit polynomial source price, including
added zero slots and the input/output endpoint copies. -/
namespace Blotto.PlayerSpecificDescriptorPadSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H N k m : ℕ) : ℕ := PlayerSpecificDescriptorCopySourceCost.coefficient*(H+N+k+1)^5+
  PlayerSpecificDescriptorCopySourceCost.coefficient*(H+N+(k+m)+1)^5+(2*(k+1)+6)

theorem cost {N k : ℕ} (root : Candidate) (d : Descriptor N k) (m : ℕ) (fallback : Fin k) (H : ℕ)
    (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4) (hmH : HasHeight root.polynomial H)
    (he : HasHeight [root.interval.lo,root.interval.hi] H) (hd : Bounds root d H) :
    (PlayerSpecificDescriptorPadExecution.run RationalCostModel.schoolbook root d m fallback).2≤work H N k m := by
  have henv : ∀ j,PlayerSpecificAlgebraicReduction.Reduced root.polynomial (PlayerSpecificDescriptorPadExecution.environment.read j) ∧
      HasHeight (PlayerSpecificDescriptorPadExecution.environment.read j) H := fun j => Fin.elim0 j
  have hi:=PlayerSpecificDescriptorCopySourceCost.cost root PlayerSpecificDescriptorPadExecution.environment d H hmH hml he henv hd
  have ho:=PlayerSpecificDescriptorCopySourceCost.cost root PlayerSpecificDescriptorPadExecution.environment
    (PlayerSpecificAlgebraicDescriptorPad.pad d m fallback) H hmH hml he henv
    (PlayerSpecificAlgebraicDescriptorPad.bounds root d m fallback H hm0 hd)
  have hp:=PlayerSpecificDescriptorPadExecution.packing_cost RationalCostModel.schoolbook fallback
  exact Nat.add_le_add (Nat.add_le_add hi ho) hp

end Blotto.PlayerSpecificDescriptorPadSourceCost
