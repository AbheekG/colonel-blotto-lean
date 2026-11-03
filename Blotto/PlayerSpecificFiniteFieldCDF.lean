import Blotto.PlayerSpecificTerminalLeafCDF
import Blotto.PlayerSpecificZeroUniformAffineCDF
import Blotto.PlayerSpecificResourceContinuationAffineCDF
import Blotto.PlayerSpecificOriginalIdealResourceLeaves

/-! The complete actual field-valued draw combines its resource prefix
and reached terminal suffix. The marginal comparison follows from native
reached leaves and affine resource means, with no target-law oracle. -/
namespace Blotto.PlayerSpecificFiniteFieldCDF
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (B : ℚ) (player : Bool)
    (H K : ℕ) (x : ℝ) : Mixed N :=
  (fairBitLaw (PlayerSpecificAlgebraicFiniteDraw.bitCount N H K)).map (fun bits =>
    PlayerSpecificAlgebraicSegment.values (PlayerSpecificAlgebraicFiniteDraw.draw p B player H K bits) x)

theorem prepared {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (B : ℚ) (player : Bool)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x (start RationalCostModel.schoolbook p player))
    (hstart : InBox (lengths p x) (eval (start RationalCostModel.schoolbook p player) x))
    (hB : 0 < (if player then 1 else B : ℚ))
    (hL : ∀ j,0 < lengths p x j ∧ lengths p x j ≤ ((if player then 1 else B : ℚ):ℝ))
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T) (hml : p.parameters.root.polynomial.length ≤ 4)
    (hBH : RationalHeight (if player then 1 else B : ℚ) T) (hsize : ∀ j,HasHeight (p.rows.read j).length T)
    (hleaves : PlayerSpecificResourceIdealLeaves.ForLeaves RationalCostModel.schoolbook p
      (fun s => Valid p x s ∧ InBox (lengths p x) (eval s x) ∧
        (∑ j,eval s x j)=2*(((if player then 1 else B : ℚ):ℝ)) ∧ s.active.length ≤ 1 ∧
          ∀ j,HasHeight (s.data.read j) T) (N-1) (start RationalCostModel.schoolbook p player))
    (H K : ℕ) (j : Fin N) (z : ℝ) :
    |closedCDF (law p B player H K x) j z-
      (zeroUniformLaw (lengths p x j) (eval (start RationalCostModel.schoolbook p player) x j/lengths p x j)).real (Set.Iic z)| ≤
        ((N-1:ℕ):ℝ)/(2:ℝ)^H+PlayerSpecificTerminalCoreCDF.error H K := by
  let b : ℚ := if player then 1 else B
  let draw := fun (s : State N) (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) =>
    PlayerSpecificAlgebraicSegment.values (PlayerSpecificAlgebraicTerminalLeafExecution.run p s b H K bits) x
  have hl : PlayerSpecificResourceIdealLeaves.ForLeaves RationalCostModel.schoolbook p
      (fun s => |closedCDF ((fairBitLaw (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K)).map (draw s)) j z-
        (PlayerSpecificZeroUniformAffineCDF.base z+PlayerSpecificZeroUniformAffineCDF.slope (lengths p x j) z*eval s x j)|
          ≤ PlayerSpecificTerminalCoreCDF.error H K) (N-1) (start RationalCostModel.schoolbook p player) := by
    apply PlayerSpecificResourceIdealLeaves.mono RationalCostModel.schoolbook p _ _ (N-1)
      (start RationalCostModel.schoolbook p player) hleaves
    intro s hstate
    have h := PlayerSpecificTerminalLeafCDF.marginal_error p s b x hc hstate.1 hB hL hstate.2.1 hstate.2.2.1
      hstate.2.2.2.1 T hroot hml hBH hsize hstate.2.2.2.2 H K j z
    rw [PlayerSpecificZeroUniformAffineCDF.formula _ _ _ (hL j).1 (hstate.2.1 j)] at h
    exact h
  have h := PlayerSpecificResourceContinuationAffineCDF.marginal_error RationalCostModel.schoolbook p x hc H (N-1)
    (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) (start RationalCostModel.schoolbook p player) hs draw j j z
      (PlayerSpecificZeroUniformAffineCDF.base z) (PlayerSpecificZeroUniformAffineCDF.slope (lengths p x j) z) _ hl
  rw [←PlayerSpecificZeroUniformAffineCDF.formula _ _ _ (hL j).1 (hstart j)] at h
  exact h

end Blotto.PlayerSpecificFiniteFieldCDF
