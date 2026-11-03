import Blotto.PlayerSpecificAlgebraicSortTriple

/-! Unsorted four-variable raw inputs execute one three-comparison sort,
retain its permutation, and supply the existing ordered finite-bit core. -/
namespace Blotto.PlayerSpecificAlgebraicFourSpecInput
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Input where
  budget : Data
  lengths : FixedArrayTable 3 Data
  mixtureLength : Data
  probability : Data

structure Values (a : Input) (i : FourSpec) (x : ℝ) : Prop where
  budget : realEvaluate a.budget x=i.B
  lengths : ∀ j,realEvaluate (a.lengths.read j) x=i.length j
  mixtureLength : realEvaluate a.mixtureLength x=i.ell
  probability : realEvaluate a.probability x=i.p

structure Fits (root : Candidate) (a : Input) (T : ℕ) : Prop where
  budget : Reduced root.polynomial a.budget ∧ HasHeight a.budget T
  lengths : ∀ j,Reduced root.polynomial (a.lengths.read j) ∧ HasHeight (a.lengths.read j) T
  mixtureLength : Reduced root.polynomial a.mixtureLength ∧ HasHeight a.mixtureLength T
  probability : Reduced root.polynomial a.probability ∧ HasHeight a.probability T

structure Prepared where
  input : PlayerSpecificAlgebraicFourInput.Input
  permutation : Equiv.Perm (Fin 3)

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) : Prepared :=
  let s := PlayerSpecificAlgebraicSortTriple.prepare model root a.lengths
  ⟨⟨a.budget,s.lengths.read 0,s.lengths.read 1,s.lengths.read 2,a.mixtureLength,a.probability⟩,s.permutation⟩

theorem values (model : RationalCostModel) (root : Candidate) (a : Input) (i : FourSpec)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : Values a i x) :
    PlayerSpecificAlgebraicFourInput.Values (prepare model root a).input i.input x ∧
      (prepare model root a).permutation=sortTriplePermutation i.length := by
  have hl : PlayerSpecificAlgebraicSegment.values a.lengths x=i.length := by funext j; exact ha.lengths j
  have hs := PlayerSpecificAlgebraicSortTriple.values model root a.lengths hm hirr hv x hx
  rw [hl] at hs
  refine ⟨⟨ha.budget,?_,?_,?_,ha.mixtureLength,ha.probability⟩,hs.2⟩
  · exact congrFun hs.1 0
  · exact congrFun hs.1 1
  · exact congrFun hs.1 2

theorem fits (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T) :
    PlayerSpecificAlgebraicFourInput.Fits root (prepare model root a).input T := by
  have hs := PlayerSpecificAlgebraicPermutation.bounds root (PlayerSpecificAlgebraicSortTriple.permutation model root a.lengths)
    a.lengths T ha.lengths
  exact ⟨ha.budget,hs 0,hs 1,hs 2,ha.mixtureLength,ha.probability⟩

end Blotto.PlayerSpecificAlgebraicFourSpecInput
