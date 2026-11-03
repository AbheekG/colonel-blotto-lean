import Blotto.PlayerSpecificOrderedThreeExecution

/-! Complete branch-sensitive ordered preparation source work. The
bound covers both continuations; execution calls exactly one of them. -/
namespace Blotto.PlayerSpecificOrderedThreeSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := PlayerSpecificThreePositiveSourceCost.coefficient+
  PlayerSpecificThreePositiveGeometrySourceCost.coefficient+PlayerSpecificThreeExceptionalSourceCost.coefficient+2

theorem positive_profile (U V W X : ℕ) (hX : 1≤X) : U*X+V*X+2≤(U+V+W+2)*X := by
  nlinarith only [hX,Nat.zero_le (W*X)]
theorem exceptional_profile (U V W X : ℕ) (hX : 1≤X) : U*X+W*X+2≤(U+V+W+2)*X := by
  nlinarith only [hX,Nat.zero_le (V*X)]

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root a H) :
    (PlayerSpecificOrderedThreeExecution.run RationalCostModel.schoolbook root a).2≤coefficient*(H+1)^3 := by
  have ht:=PlayerSpecificThreePositiveSourceCost.cost root a H hm hm0 hml hmH he hv hH ha
  have hg:=PlayerSpecificThreePositiveGeometrySourceCost.cost root a H hm hm0 hml hmH he hv hH ha
  have hexc:=PlayerSpecificThreeExceptionalSourceCost.cost root a H hm hm0 hml hmH he hv hH ha
  have hX : 1≤(H+1)^3 := Nat.succ_le_of_lt (pow_pos (by omega : 0<H+1) 3)
  have hpack : PlayerSpecificRationalTrace.price RationalCostModel.schoolbook [.control 1]=2 := rfl
  simp only [PlayerSpecificOrderedThreeExecution.run,hpack]
  split
  · exact (Nat.add_le_add_right (Nat.add_le_add ht hg) 2).trans (positive_profile _ _ _ _ hX)
  · exact (Nat.add_le_add_right (Nat.add_le_add ht hexc) 2).trans (exceptional_profile _ _ _ _ hX)

end Blotto.PlayerSpecificOrderedThreeSourceCost
