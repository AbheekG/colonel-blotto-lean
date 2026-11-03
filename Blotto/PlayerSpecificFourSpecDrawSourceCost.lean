import Blotto.PlayerSpecificFourSpecDrawExecution

/-! Complete original-input source work for unsorted four-variable
sampling, including stable sorting, selected ordered draw and restoration. -/
namespace Blotto.PlayerSpecificFourSpecDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourSpecInput PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frameHeight (T K : ℕ) : ℕ :=
  max T (PlayerSpecificAlgebraicOrderedFourDraw.height T K)+4

def work (T H K : ℕ) : ℕ :=
  PlayerSpecificFourSpecInputSourceCost.work T+
  PlayerSpecificOrderedFourDrawSourceCost.work T H K+
  (1812*PlayerSpecificResourceCostProfile.rationalCoefficient)*(frameHeight T K+1)^3+2

theorem cost (r : PlayerSpecificFiniteParameterReturn.Result)
    (a : Input) (i : FourSpec) (x : ℝ) (T H K : ℕ)
    (bits : Fin ((80*H+K)+K) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourSpecInput.Values a i x)
    (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2 ≤ T) :
    (PlayerSpecificFourSpecDrawExecution.run r a H K bits).2 ≤ work T H K := by
  let model := RationalCostModel.schoolbook
  let S := frameHeight T K
  let W := PlayerSpecificAlgebraicComparisonExecution.width S
  let prepared := PlayerSpecificFourSpecInputExecution.run r.root a
  let p := prepared.1
  let ordered := PlayerSpecificOrderedFourDrawExecution.run r p.input H K bits
  let y := ordered.1
  let result := PlayerSpecificFourSpecDrawExecution.restored p y
  have hm0 : r.root.polynomial ≠ [] := by
    intro hz
    exact hirr.ne_zero (by rw [hz]; rfl)
  have hinput := PlayerSpecificFourSpecInputSourceCost.cost r.root a T
    hm hm0 hml hmT he hv hT hfit
  have hpvalue : PlayerSpecificAlgebraicFourInput.Values p.input i.input x := by
    dsimp only [p,prepared]
    rw [PlayerSpecificFourSpecInputExecution.value]
    exact (PlayerSpecificAlgebraicFourSpecInput.values model r.root a i hm hirr hv x hx ha).1
  have hpfit : PlayerSpecificAlgebraicFourInput.Fits r.root p.input T := by
    dsimp only [p,prepared]
    rw [PlayerSpecificFourSpecInputExecution.value]
    exact PlayerSpecificAlgebraicFourSpecInput.fits model r.root a T hfit
  have hordered := PlayerSpecificOrderedFourDrawSourceCost.cost r p.input i.input x T H K bits
    hm hirr hv hx hpvalue hpfit hml hmT he hT
  have hy : ∀ j,Reduced r.root.polynomial (y.read j) ∧
      HasHeight (y.read j) (PlayerSpecificAlgebraicOrderedFourDraw.height T K) := by
    dsimp only [y,ordered]
    rw [PlayerSpecificOrderedFourDrawExecution.value]
    exact PlayerSpecificAlgebraicOrderedFourDraw.bounds r p.input i.input hm hirr hv x hx
      hpvalue T hpfit hml hmT hT H K bits
  have hresult : ∀ j,Reduced r.root.polynomial (result.read j) ∧
      HasHeight (result.read j) (PlayerSpecificAlgebraicOrderedFourDraw.height T K) :=
    PlayerSpecificAlgebraicPermutation.bounds r.root
      (rationalPermutationWithLast p.permutation).symm y _ hy
  have hTS : T ≤ S := by dsimp [S,frameHeight]; omega
  have hYS : PlayerSpecificAlgebraicOrderedFourDraw.height T K ≤ S := by
    dsimp [S,frameHeight]; omega
  have hf := PlayerSpecificExpressionVectorFrameCost.cost model r.root y result S
    (mono hmT hTS) hml (mono he hTS)
    (fun j => ⟨mono (hy j).2 hYS,by have h := (hy j).1.2; omega⟩)
    (fun j => ⟨mono (hresult j).2 hYS,by have h := (hresult j).1.2; omega⟩)
    (by dsimp [S,frameHeight]; omega) (by dsimp [S,frameHeight]; omega)
    (by dsimp [S,frameHeight]; omega)
  have hf' : price model (PlayerSpecificExpressionVectorExecution.frame r.root y result) ≤
      (1800*PlayerSpecificResourceCostProfile.rationalCoefficient)*(S+1)^3 :=
    hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 1800 S)
  have hw : ∀ word ∈ List.ofFn (fun j : Fin 4 =>
      ((rationalPermutationWithLast p.permutation).symm j).val), binaryWordWidth word ≤ W := by
    intro word hword
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hword
    have hle : ((rationalPermutationWithLast p.permutation).symm j).val ≤ S := by
      have hj := ((rationalPermutationWithLast p.permutation).symm j).isLt
      dsimp [S,frameHeight]
      omega
    exact (control_width _).trans
      ((Nat.add_le_add_right hle 1).trans
        (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hwords := PlayerSpecificAlgebraicCallerFrame.controls_cost model
    (List.ofFn (fun j : Fin 4 => ((rationalPermutationWithLast p.permutation).symm j).val))
    W hw (by have h := (PlayerSpecificAlgebraicActiveListCost.width_large S).1; omega)
  have hwords' : price model (List.ofFn (fun j : Fin 4 =>
      Event.control ((rationalPermutationWithLast p.permutation).symm j).val)) ≤
      (12*PlayerSpecificResourceCostProfile.rationalCoefficient)*(S+1)^3 := by
    change price model ((List.ofFn (fun j : Fin 4 =>
      ((rationalPermutationWithLast p.permutation).symm j).val)).map Event.control) ≤ _
    simpa only [List.length_ofFn] using
      hwords.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 12 S)
  change prepared.2+ordered.2+
    price model (PlayerSpecificFourSpecDrawExecution.frame r.root p y result)+
    price model [.control 1] ≤ _
  rw [PlayerSpecificFourSpecDrawExecution.frame,price_append,
    show price model [.control 1]=2 by rfl]
  have hsum := Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add hinput hordered) (Nat.add_le_add hf' hwords')) 2
  apply hsum.trans_eq
  dsimp only [S]
  unfold work
  ring

theorem same_return_and_cost (r : PlayerSpecificFiniteParameterReturn.Result)
    (a : Input) (i : FourSpec) (x : ℝ) (T H K : ℕ)
    (bits : Fin ((80*H+K)+K) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourSpecInput.Values a i x)
    (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2 ≤ T) :
    (PlayerSpecificFourSpecDrawExecution.run r a H K bits).1 =
      PlayerSpecificAlgebraicFourSpecDraw.draw r a H K bits ∧
    (PlayerSpecificFourSpecDrawExecution.run r a H K bits).2 ≤ work T H K :=
  ⟨PlayerSpecificFourSpecDrawExecution.value r a H K bits,
    cost r a i x T H K bits hm hirr hv hx ha hfit hml hmT he hT⟩

end Blotto.PlayerSpecificFourSpecDrawSourceCost
