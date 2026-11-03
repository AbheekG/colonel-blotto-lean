import Blotto.PlayerSpecificTerminalCoreDrawExecution
import Blotto.PlayerSpecificAlgebraicTerminalCoreDrawBounds

/-! The reached terminal continuation pays for one addressed packet and
exactly one of the four native draw branches. -/
namespace Blotto.PlayerSpecificTerminalCoreSelectedSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicTerminalCoreInput PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (T H K : ℕ) : ℕ :=
  PlayerSpecificBitSlicePolynomial.coefficient*(PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K+1)^3+
  PlayerSpecificComplementaryDrawSourceCost.work T K+
  PlayerSpecificThreeDrawSourceCost.coefficient*(T+H+K+1)^16+
  PlayerSpecificThreeDrawSourceCost.coefficient*(step T+H+K+1)^16+
  PlayerSpecificFourSpecDrawSourceCost.work T H K+
  (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(T+1)^3+2

theorem cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input)
    (x : ℝ) (T H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : Valid a x) (hfit : PlayerSpecificAlgebraicTerminalCoreFits.Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T) (hT : 2 ≤ T) :
    (PlayerSpecificTerminalCoreDrawExecution.selected r a H K bits).2 ≤ work T H K := by
  let model := RationalCostModel.schoolbook
  let M := PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K
  let short := PlayerSpecificBitSliceExecution.run model M 0 (8*H+K)
    (by dsimp only [M]; simpa only [Nat.zero_add] using PlayerSpecificAlgebraicTerminalCoreDraw.three_bit_bound H K) bits
  let midpoint := PlayerSpecificBitSliceExecution.run model M 0 K
    (by dsimp only [M]; simpa only [Nat.zero_add] using PlayerSpecificAlgebraicTerminalCoreDraw.midpoint_bit_bound H K) bits
  have hm0 : r.root.polynomial ≠ [] := by
    intro hz
    exact hirr.ne_zero (by rw [hz]; rfl)
  have hshort := PlayerSpecificBitSlicePolynomial.cost M 0 (8*H+K)
    (by dsimp only [M]; simpa only [Nat.zero_add] using PlayerSpecificAlgebraicTerminalCoreDraw.three_bit_bound H K) bits
  have hmidpoint := PlayerSpecificBitSlicePolynomial.cost M 0 K
    (by dsimp only [M]; simpa only [Nat.zero_add] using PlayerSpecificAlgebraicTerminalCoreDraw.midpoint_bit_bound H K) bits
  by_cases hc : a.count=2
  · cases hf : a.fractional with
    | none =>
      let drawn := PlayerSpecificComplementaryDrawExecution.run r.root a.budget K midpoint.1
      have hd := PlayerSpecificComplementaryDrawSourceCost.cost r.root a.budget T K midpoint.1
        hm hm0 hml hmT he hv hT hfit.budget
      simp only [PlayerSpecificTerminalCoreDrawExecution.selected,hc,ite_true,hf]
      change midpoint.2+drawn.2+price model [.control 1] ≤ _
      rw [show price model [.control 1]=2 by rfl]
      have hsum := Nat.add_le_add_right (Nat.add_le_add hmidpoint hd) 2
      dsimp only [M] at hsum
      exact hsum.trans (by unfold work; omega)
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      let drawn := PlayerSpecificThreeDrawExecution.run model r.root (mixedThree a ell probability) H K short.1
      have hd := PlayerSpecificThreeDrawSourceCost.cost r.root (mixedThree a ell probability) T H K short.1
        hm hm0 hml hmT he hv hT
        (PlayerSpecificAlgebraicTerminalCoreFits.mixed_two r.root a T hfit ell probability hf)
      simp only [PlayerSpecificTerminalCoreDrawExecution.selected,hc,ite_true,hf]
      change short.2+drawn.2+price model [.control 1] ≤ _
      rw [show price model [.control 1]=2 by rfl]
      have hsum := Nat.add_le_add_right (Nat.add_le_add hshort hd) 2
      dsimp only [M] at hsum
      exact hsum.trans (by unfold work; omega)
  · have hc3 : a.count=3 := ha.count.resolve_left hc
    cases hf : a.fractional with
    | none =>
      let one := PlayerSpecificFieldCombinationContract.constant r.root.polynomial 1
      let input : PlayerSpecificAlgebraicThreeInput.Input :=
        ⟨a.budget,a.lengths.read 0,a.lengths.read 1,a.lengths.read 2,one.1⟩
      let drawn := PlayerSpecificThreeDrawExecution.run model r.root input H K short.1
      have hle : T ≤ step T := (Nat.le_succ _).trans (large T)
      have hOne := PlayerSpecificAlgebraicExpressionPrimitiveCost.constant_cost model r.root 1 T
        hm hm0 hml hmT (one_height.mono (by omega)) (by omega)
      have hOne' := hOne.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 T)
      have hinput : input=uniformThree r.root a := by
        dsimp only [input,uniformThree,one]
        rw [PlayerSpecificFieldCombinationContract.constant_value]
      have hd : drawn.2 ≤ PlayerSpecificThreeDrawSourceCost.coefficient*(step T+H+K+1)^16 := by
        dsimp only [drawn]
        rw [hinput]
        exact PlayerSpecificThreeDrawSourceCost.cost r.root (uniformThree r.root a) (step T) H K short.1
          hm hm0 hml (mono hmT hle) (mono he hle) hv (hT.trans hle)
          (PlayerSpecificAlgebraicTerminalCoreFits.uniform r.root a T hfit hm hm0 hml hmT (by omega))
      simp only [PlayerSpecificTerminalCoreDrawExecution.selected,hc,ite_false,hf]
      change price model one.2+short.2+drawn.2+price model [.control 1] ≤ _
      rw [show price model [.control 1]=2 by rfl]
      have hsum := Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add hOne' hshort) hd) 2
      dsimp only [M] at hsum
      exact hsum.trans (by unfold work; omega)
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      let drawn := PlayerSpecificFourSpecDrawExecution.run r (mixedFour a ell probability) H K bits
      let i := mixedSpecThree a x ha hc3 ell probability hf
      have hd := PlayerSpecificFourSpecDrawSourceCost.cost r (mixedFour a ell probability) i.fourInput
        x T H K bits hm hirr hv hx (mixed_three_values a x ha hc3 ell probability hf)
        (PlayerSpecificAlgebraicTerminalCoreFits.mixed_three r.root a T hfit ell probability hf)
        hml hmT he hT
      simp only [PlayerSpecificTerminalCoreDrawExecution.selected,hc,ite_false,hf]
      change drawn.2+price model [.control 1] ≤ _
      rw [show price model [.control 1]=2 by rfl]
      have hsum := Nat.add_le_add_right hd 2
      exact hsum.trans (by unfold work; omega)

end Blotto.PlayerSpecificTerminalCoreSelectedSourceCost
