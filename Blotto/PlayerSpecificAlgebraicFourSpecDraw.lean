import Blotto.PlayerSpecificAlgebraicFourSpecInput

/-! Actual unsorted four-variable sampling restores the three uniform
coordinates while keeping the mixture coordinate last. -/
namespace Blotto.PlayerSpecificAlgebraicFourSpecDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicFourSpecInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def draw (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin ((80*H+K)+K) → Bool) : FixedArrayTable 4 Data :=
  let p := prepare RationalCostModel.schoolbook r.root a
  let y := PlayerSpecificAlgebraicOrderedFourDraw.draw r p.input H K bits
  PlayerSpecificAlgebraicPermutation.permute (rationalPermutationWithLast p.permutation).symm y

theorem every_path (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourSpec)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourSpecInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (H K : ℕ) (bits : Fin ((80*H+K)+K) → Bool) : FullBudget i.B (PlayerSpecificAlgebraicSegment.values (draw r a H K bits) x) := by
  let p := prepare RationalCostModel.schoolbook r.root a
  let y := PlayerSpecificAlgebraicOrderedFourDraw.draw r p.input H K bits
  have hp := PlayerSpecificAlgebraicFourSpecInput.values RationalCostModel.schoolbook r.root a i hm hirr hv x hx ha
  have hf := fits RationalCostModel.schoolbook r.root a T hfit
  have hy := PlayerSpecificAlgebraicOrderedFourDraw.every_path r p.input i.input hm hirr hv x hx hp.1 T hf hml hmT hT H K bits
  change FullBudget i.B (PlayerSpecificAlgebraicSegment.values
    (PlayerSpecificAlgebraicPermutation.permute (rationalPermutationWithLast p.permutation).symm y) x)
  rw [PlayerSpecificAlgebraicPermutation.value]
  exact permuteAllocation_fullBudget _ hy

theorem permutation_value (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourSpec)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourSpecInput.Values a i x) :
    (rationalPermutationWithLast (prepare RationalCostModel.schoolbook r.root a).permutation).symm=
      (permutationWithLast (sortTriplePermutation i.length)).symm := by
  rw [(PlayerSpecificAlgebraicFourSpecInput.values RationalCostModel.schoolbook r.root a i hm hirr hv x hx ha).2]
  rfl

theorem bounds (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourSpec)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourSpecInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (H K : ℕ) (bits : Fin ((80*H+K)+K) → Bool) :
    ∀ j,Reduced r.root.polynomial ((draw r a H K bits).read j) ∧
      HasHeight ((draw r a H K bits).read j) (PlayerSpecificAlgebraicOrderedFourDraw.height T K) := by
  let p := prepare RationalCostModel.schoolbook r.root a
  have hp := PlayerSpecificAlgebraicFourSpecInput.values RationalCostModel.schoolbook r.root a i hm hirr hv x hx ha
  have hf := fits RationalCostModel.schoolbook r.root a T hfit
  have hy := PlayerSpecificAlgebraicOrderedFourDraw.bounds r p.input i.input hm hirr hv x hx hp.1 T hf hml hmT hT H K bits
  exact PlayerSpecificAlgebraicPermutation.bounds r.root _ _ _ hy

theorem linear_heights (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourSpec)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourSpecInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (H K : ℕ) (bits : Fin ((80*H+K)+K) → Bool) :
    ∀ j,HasHeight ((draw r a H K bits).read j) (PlayerSpecificAlgebraicOrderedFourDraw.coefficient*(T+K+1)) := by
  intro j
  exact PlayerSpecificPolynomialHeights.mono (bounds r a i hm hirr hv x hx ha T hfit hml hmT hT H K bits j).2
    ((Nat.le_succ _).trans (PlayerSpecificAlgebraicOrderedFourDraw.height_linear T K))

theorem last_read (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin ((80*H+K)+K) → Bool) : (draw r a H K bits).read 3=
      (PlayerSpecificAlgebraicOrderedFourDraw.draw r (prepare RationalCostModel.schoolbook r.root a).input H K bits).read 3 := by
  simp only [draw,PlayerSpecificAlgebraicPermutation.permute,FixedArrayTable.read_ofFn,
    rationalPermutationWithLast_real]
  exact congrArg (fun j => (PlayerSpecificAlgebraicOrderedFourDraw.draw r
    (prepare RationalCostModel.schoolbook r.root a).input H K bits).read j) (permutationWithLast_symm_last _)

theorem random_bit_budget (N H K : ℕ) : (80*H+K)+K ≤ (N+1000)*H+2*K :=
  PlayerSpecificAlgebraicOrderedFourDraw.random_bit_budget N H K

end Blotto.PlayerSpecificAlgebraicFourSpecDraw
