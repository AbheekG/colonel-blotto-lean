import Blotto.PlayerSpecificAlgebraicOrderedFourDraw
import Blotto.RationalSortTriple

/-! Native cached-array permutations preserve all row sizes and exactly
implement the corresponding real allocation permutation. -/
namespace Blotto.PlayerSpecificAlgebraicPermutation
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false

def permute {N : ℕ} (p : Equiv.Perm (Fin N)) (a : FixedArrayTable N Data) : FixedArrayTable N Data :=
  FixedArrayTable.ofFn (fun j => a.read (p j))

theorem value {N : ℕ} (p : Equiv.Perm (Fin N)) (a : FixedArrayTable N Data) (x : ℝ) :
    values (permute p a) x=permuteAllocation p (values a x) := by
  funext j
  simp only [permute,values,FixedArrayTable.read_ofFn,permuteAllocation]

theorem bounds {N : ℕ} (root : Candidate) (p : Equiv.Perm (Fin N)) (a : FixedArrayTable N Data) (T : ℕ)
    (ha : ∀ j,Reduced root.polynomial (a.read j) ∧ HasHeight (a.read j) T) :
    ∀ j,Reduced root.polynomial ((permute p a).read j) ∧ HasHeight ((permute p a).read j) T := by
  intro j
  rw [permute,FixedArrayTable.read_ofFn]
  exact ha (p j)

end Blotto.PlayerSpecificAlgebraicPermutation
