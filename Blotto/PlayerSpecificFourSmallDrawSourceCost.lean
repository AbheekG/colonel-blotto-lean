import Blotto.PlayerSpecificFourSmallDrawExecution

/-! Complete source price for the small four-variable coin and only its
reached merged or reflected continuation. The envelope lists both branch
prices but execution visits just one. -/
namespace Blotto.PlayerSpecificFourSmallDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (T H K : ℕ) : ℕ :=
  PlayerSpecificBitSlicePolynomial.coefficient*(PlayerSpecificAlgebraicFourSmallDraw.bitCount H K+1)^3+
  PlayerSpecificBitSlicePolynomial.coefficient*(PlayerSpecificAlgebraicFourSmallDraw.bitCount H K+1)^3+
  PlayerSpecificAlgebraicCoinCost.polynomialCoefficient*(T+H+3)^3+
  PlayerSpecificBitSlicePolynomial.coefficient*(PlayerSpecificAlgebraicFourSmallDraw.remaining H K+1)^3+
  PlayerSpecificFourMergedDrawSourceCost.work T H K+
  PlayerSpecificFourReflectedDrawSourceCost.work T H K+2

theorem cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (x : ℝ) (T H K : ℕ) (bits : Fin (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo<r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length≤4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2≤T)
    (hcase : i.w < (1-i.p)*i.ell) :
    (PlayerSpecificFourSmallDrawExecution.run r a H K bits).2≤work T H K := by
  let model:=RationalCostModel.schoolbook
  let R:=PlayerSpecificAlgebraicFourSmallDraw.remaining H K
  let M:=PlayerSpecificAlgebraicFourSmallDraw.bitCount H K
  let head:=PlayerSpecificBitSliceExecution.run model M 0 H (by dsimp only [M,PlayerSpecificAlgebraicFourSmallDraw.bitCount]; omega) bits
  let rest:=PlayerSpecificBitSliceExecution.run model M H R (by dsimp only [M,PlayerSpecificAlgebraicFourSmallDraw.bitCount]; omega) bits
  let coin:=PlayerSpecificAlgebraicCoinExecution.run model r.root a.probability H head.1
  let headBits:=PlayerSpecificBitSliceExecution.run model R 0 (8*H+K)
    (by simpa only [Nat.zero_add] using PlayerSpecificAlgebraicFourSmallDraw.uniform_bit_bound H K) rest.1
  let merged:=PlayerSpecificFourMergedDrawExecution.run model r.root a H K headBits.1
  let reflected:=PlayerSpecificFourReflectedDrawExecution.run r a H K rest.1
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hhead:=PlayerSpecificBitSlicePolynomial.cost M 0 H (by dsimp only [M,PlayerSpecificAlgebraicFourSmallDraw.bitCount]; omega) bits
  have hrest:=PlayerSpecificBitSlicePolynomial.cost M H R (by dsimp only [M,PlayerSpecificAlgebraicFourSmallDraw.bitCount]; omega) bits
  have hcoin:=PlayerSpecificAlgebraicCoinCost.cost r.root a.probability T H head.1 hm hm0 hml hmT he hv
    hfit.probability.2 hfit.probability.1
  have hheadBits:=PlayerSpecificBitSlicePolynomial.cost R 0 (8*H+K)
    (by simpa only [Nat.zero_add] using PlayerSpecificAlgebraicFourSmallDraw.uniform_bit_bound H K) rest.1
  have hmerged:=PlayerSpecificFourMergedDrawSourceCost.cost r.root a T H K headBits.1
    hm hm0 hml hmT he hv hT hfit
  have hreflected:=PlayerSpecificFourReflectedDrawSourceCost.cost r a i x T H K rest.1
    hm hirr hv hx ha hfit hml hmT he hT hcase
  dsimp only [PlayerSpecificFourSmallDrawExecution.run]
  split
  · change head.2+rest.2+coin.2+headBits.2+merged.2+price model [.control 1]≤_
    rw [show price model [.control 1]=2 by rfl]
    have hsum:=Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add hhead hrest) hcoin) hheadBits) hmerged) 2
    dsimp only [M,R] at hsum
    exact hsum.trans (by unfold work; omega)
  · change head.2+rest.2+coin.2+reflected.2+price model [.control 1]≤_
    rw [show price model [.control 1]=2 by rfl]
    have hsum:=Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add hhead hrest) hcoin) hreflected) 2
    dsimp only [M,R] at hsum
    exact hsum.trans (by unfold work; omega)

theorem same_return_and_cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (x : ℝ) (T H K : ℕ) (bits : Fin (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo<r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length≤4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2≤T)
    (hcase : i.w < (1-i.p)*i.ell) :
    (PlayerSpecificFourSmallDrawExecution.run r a H K bits).1=PlayerSpecificAlgebraicFourSmallDraw.draw r a H K bits ∧
    (PlayerSpecificFourSmallDrawExecution.run r a H K bits).2≤work T H K :=
  ⟨PlayerSpecificFourSmallDrawExecution.value r a H K bits,
    cost r a i x T H K bits hm hirr hv hx ha hfit hml hmT he hT hcase⟩

end Blotto.PlayerSpecificFourSmallDrawSourceCost
