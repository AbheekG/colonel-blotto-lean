import Blotto.PlayerSpecificNestedCaseParameterSourceCost

/-! Complete descriptor-copy frames, with dimensions and coefficient
sizes taken from the actual input and returned arrays. -/
namespace Blotto.PlayerSpecificDescriptorCopySourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicReduction
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 40000*PlayerSpecificResourceCostProfile.rationalCoefficient

theorem cardinal (k n m S : ℕ) (hk : k≤S) (hn : n≤S) (hm : m≤S) (hS : 1≤S) :
    k+m*(2*n+1)+1≤5*S^2 := by
  have hp:=Nat.mul_le_mul hm (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hn) 1)
  have hs:=Nat.mul_le_mul_right S hS
  nlinarith only [hp,hs,hk,hS]

theorem polynomial (C k n m S : ℕ) (hk : k≤S) (hn : n≤S) (hm : m≤S) (hS : 1≤S) :
    (1000*(k+m*(2*n+1)+1)*C)*(S+1)^3≤(40000*C)*S^5 := by
  have hc:=cardinal k n m S hk hn hm hS
  have hp:=Nat.pow_le_pow_left (show S+1≤2*S by omega) 3
  have hmul:=Nat.mul_le_mul (Nat.mul_le_mul_right C (Nat.mul_le_mul_left 1000 hc)) hp
  exact hmul.trans_eq (by ring)

theorem cost {k n m : ℕ} (root : Candidate) (env : FixedArrayTable k Data) (d : Descriptor n m) (H : ℕ)
    (hm : HasHeight root.polynomial H) (hml : root.polynomial.length≤4)
    (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H)
    (hd : Bounds root d H) :
    price RationalCostModel.schoolbook (PlayerSpecificDescriptorProgramExecution.frame root env d)≤
      coefficient*(H+n+m+k+1)^5 := by
  let S:=H+n+m+k+1
  have hHS : H≤S := by dsimp [S]; omega
  have hk : k≤S := by dsimp [S]; omega
  have hn : n≤S := by dsimp [S]; omega
  have hms : m≤S := by dsimp [S]; omega
  have hS : 1≤S := by dsimp [S]; omega
  have hrows : ∀ row∈PlayerSpecificDescriptorProgramExecution.rows d,HasHeight row S ∧ row.length≤3 := by
    refine PlayerSpecificDescriptorProgramFrameCost.rows_property d (fun row => HasHeight row S ∧ row.length≤3) ?_ ?_ ?_
    · intro slot; exact ⟨mono (hd.weights slot).2 hHS,by have h:=(hd.weights slot).1.2; omega⟩
    · intro slot j; exact ⟨mono (hd.first slot j).2 hHS,by have h:=(hd.first slot j).1.2; omega⟩
    · intro slot j; exact ⟨mono (hd.second slot j).2 hHS,by have h:=(hd.second slot j).1.2; omega⟩
  have hf:=PlayerSpecificDescriptorProgramFrameCost.cost RationalCostModel.schoolbook root env d S
    (mono hm hHS) hml (mono he hHS)
    (fun j => ⟨mono (hEnv j).2 hHS,by have h:=(hEnv j).1.2; omega⟩) hrows hk hn hms hS
  exact (hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial _ S)).trans
    (polynomial PlayerSpecificResourceCostProfile.rationalCoefficient k n m S hk hn hms hS)

end Blotto.PlayerSpecificDescriptorCopySourceCost
