import Blotto.PlayerSpecificOrderedFourGuardSourceCost

/-! The complete ordered four-variable draw prices its guard, exactly one
addressed bit prefix, and only the reached normal or small sampler. -/
namespace Blotto.PlayerSpecificOrderedFourDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (T H K : ℕ) : ℕ :=
  PlayerSpecificOrderedFourGuardSourceCost.work T+
  PlayerSpecificBitSlicePolynomial.coefficient*((80*H+K)+K+1)^3+
  PlayerSpecificFourGluingDrawSourceCost.work T H K+
  PlayerSpecificFourSmallDrawSourceCost.work T H K+2

theorem cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (x : ℝ) (T H K : ℕ) (bits : Fin ((80*H+K)+K) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2 ≤ T) :
    (PlayerSpecificOrderedFourDrawExecution.run r a H K bits).2 ≤ work T H K := by
  let model := RationalCostModel.schoolbook
  let M := (80*H+K)+K
  let g := PlayerSpecificOrderedFourDrawExecution.guard r a
  let normalBits := PlayerSpecificBitSliceExecution.run model M 0 (80*H+K) (by dsimp only [M]; omega) bits
  let smallBits := PlayerSpecificBitSliceExecution.run model M 0
    (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K)
    (by dsimp only [M]; simpa only [Nat.zero_add] using PlayerSpecificAlgebraicOrderedFourDraw.small_bit_bound H K) bits
  let normalDraw := PlayerSpecificFourGluingDrawExecution.run model r.root a H K normalBits.1
  let smallDraw := PlayerSpecificFourSmallDrawExecution.run r a H K smallBits.1
  have hm0 : r.root.polynomial ≠ [] := by
    intro hz
    exact hirr.ne_zero (by rw [hz]; rfl)
  have hg := PlayerSpecificOrderedFourGuardSourceCost.cost r a T hm hm0 hml hmT he hv hT hfit
  have hnBits := PlayerSpecificBitSlicePolynomial.cost M 0 (80*H+K)
    (by dsimp only [M]; omega) bits
  have hsBits := PlayerSpecificBitSlicePolynomial.cost M 0
    (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K)
    (by dsimp only [M]; simpa only [Nat.zero_add] using PlayerSpecificAlgebraicOrderedFourDraw.small_bit_bound H K) bits
  have hnDraw := PlayerSpecificFourGluingDrawSourceCost.cost r.root a T H K normalBits.1
    hm hm0 hml hmT he hv hT hfit
  have hsemantic : g.1 = true ↔ (1-i.p)*i.ell ≤ i.w := by
    change (PlayerSpecificOrderedFourDrawExecution.guard r a).1 = true ↔ _
    rw [PlayerSpecificOrderedFourDrawExecution.guard_value]
    exact PlayerSpecificAlgebraicOrderedFourDraw.normal_correct r a i hm hirr hv x hx ha
  dsimp only [PlayerSpecificOrderedFourDrawExecution.run]
  split
  · change g.2 + normalBits.2 + normalDraw.2 + price model [.control 1] ≤ _
    rw [show price model [.control 1] = 2 by rfl]
    have hsum := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hg hnBits) hnDraw) 2
    dsimp only [M] at hsum
    exact hsum.trans (by unfold work; omega)
  · rename_i hbranch
    have hcase : i.w < (1-i.p)*i.ell := by
      apply lt_of_not_ge
      intro hnormal
      exact hbranch (hsemantic.mpr hnormal)
    have hsDraw := PlayerSpecificFourSmallDrawSourceCost.cost r a i x T H K smallBits.1
      hm hirr hv hx ha hfit hml hmT he hT hcase
    change g.2 + smallBits.2 + smallDraw.2 + price model [.control 1] ≤ _
    rw [show price model [.control 1] = 2 by rfl]
    have hsum := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hg hsBits) hsDraw) 2
    dsimp only [M] at hsum
    exact hsum.trans (by unfold work; omega)

theorem same_return_and_cost (r : PlayerSpecificFiniteParameterReturn.Result)
    (a : Input) (i : FourInput) (x : ℝ) (T H K : ℕ)
    (bits : Fin ((80*H+K)+K) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2 ≤ T) :
    (PlayerSpecificOrderedFourDrawExecution.run r a H K bits).1 =
      PlayerSpecificAlgebraicOrderedFourDraw.draw r a H K bits ∧
    (PlayerSpecificOrderedFourDrawExecution.run r a H K bits).2 ≤ work T H K :=
  ⟨PlayerSpecificOrderedFourDrawExecution.value r a H K bits,
    cost r a i x T H K bits hm hirr hv hx ha hfit hml hmT he hT⟩

end Blotto.PlayerSpecificOrderedFourDrawSourceCost
