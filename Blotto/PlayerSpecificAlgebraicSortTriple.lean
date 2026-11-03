import Blotto.PlayerSpecificAlgebraicPermutation

/-! Three actual selected-root comparisons sort the three uniform group
lengths and retain the exact source permutation, including equal lengths. -/
namespace Blotto.PlayerSpecificAlgebraicSortTriple
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def compare (model : RationalCostModel) (root : Candidate) (a : FixedArrayTable 3 Data) (i j : Fin 3) : Equiv.Perm (Fin 3) :=
  if PlayerSpecificAlgebraicPairStep.le model root (a.read i) (a.read j) then Equiv.refl _ else Equiv.swap i j

def permutation (model : RationalCostModel) (root : Candidate) (a : FixedArrayTable 3 Data) : Equiv.Perm (Fin 3) :=
  let p := compare model root a 0 1
  let M := PlayerSpecificAlgebraicPermutation.permute p a
  let q := compare model root M 1 2
  let N := PlayerSpecificAlgebraicPermutation.permute q M
  let r := compare model root N 0 1
  (r.trans q).trans p

structure Prepared where
  lengths : FixedArrayTable 3 Data
  permutation : Equiv.Perm (Fin 3)

def prepare (model : RationalCostModel) (root : Candidate) (a : FixedArrayTable 3 Data) : Prepared :=
  let p := permutation model root a
  ⟨PlayerSpecificAlgebraicPermutation.permute p a,p⟩

theorem compare_value (model : RationalCostModel) (root : Candidate) (a : FixedArrayTable 3 Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (i j : Fin 3) :
    compare model root a i j=comparePermutation (values a x) i j := by
  classical
  have hc := PlayerSpecificAlgebraicPairStep.le_correct model root (a.read i) (a.read j) hm hirr hv x hx
  by_cases h : realEvaluate (a.read i) x ≤ realEvaluate (a.read j) x
  · simp only [compare,ite_eq_left (hc.mpr h),comparePermutation,PlayerSpecificAlgebraicSegment.values,h,ite_true]
  · simp only [compare,ite_eq_right (fun he => h (hc.mp he)),comparePermutation,PlayerSpecificAlgebraicSegment.values,h,ite_false]

theorem permutation_value (model : RationalCostModel) (root : Candidate) (a : FixedArrayTable 3 Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    permutation model root a=sortTriplePermutation (values a x) := by
  unfold permutation sortTriplePermutation
  simp only [compare_value model root _ hm hirr hv x hx,PlayerSpecificAlgebraicPermutation.value]

theorem values (model : RationalCostModel) (root : Candidate) (a : FixedArrayTable 3 Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    PlayerSpecificAlgebraicSegment.values (prepare model root a).lengths x=sortedTriple (PlayerSpecificAlgebraicSegment.values a x) ∧
      (prepare model root a).permutation=sortTriplePermutation (PlayerSpecificAlgebraicSegment.values a x) := by
  have hp := permutation_value model root a hm hirr hv x hx
  refine ⟨?_,hp⟩
  rw [prepare,PlayerSpecificAlgebraicPermutation.value,hp]
  rfl

end Blotto.PlayerSpecificAlgebraicSortTriple
