import Blotto.PlayerSpecificResourceEntryInput

/-! Shared original-input polynomial calibration for the complete
resource entry's initialization, fair blocks, loop and returned frame. -/
namespace Blotto.PlayerSpecificResourceEntryPriceProfile
open PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def startCoefficient : ℕ := (2*PlayerSpecificAlgebraicComparisonExecution.coefficient+603)*
  PlayerSpecificResourceCostProfile.rationalCoefficient
def frameCoefficient : ℕ := 1000*PlayerSpecificResourceCostProfile.rationalCoefficient
def coefficient : ℕ := (startCoefficient+frameCoefficient)*(PlayerSpecificAlgebraicFiniteDrawHeights.baseCoefficient+1)^3+
  PlayerSpecificResourceBlockPolynomial.coefficient+PlayerSpecificResourceSourcePolynomial.coefficient

theorem transfer (C D N A U : ℕ) (hU : U+1≤D*(N+1)^2*A) :
    (N+1)*C*(U+1)^3≤(C*D^3)*(N+1)^7*A^3 := by
  simpa only [Nat.one_mul] using PlayerSpecificResourceSourcePolynomial.transfer C D 1 N A U U hU (by simp)

theorem block_transfer (N L H : ℕ) :
    PlayerSpecificResourceBlockPolynomial.coefficient*(N-1+1)^3*(H+1)^3≤
      PlayerSpecificResourceBlockPolynomial.coefficient*(N+1)^7*(L+H+1)^3 := by
  have hn : (N-1+1)^3≤(N+1)^7 := (Nat.pow_le_pow_left (show N-1+1≤N+1 by omega) 3).trans
    (Nat.pow_le_pow_right (by omega) (by decide))
  have hh : (H+1)^3≤(L+H+1)^3 := Nat.pow_le_pow_left (by omega) 3
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hn) hh

theorem multiply_profile (N C U R D : ℕ) (h : C*(U+1)*R≤C*D*(U+1)^3) :
    N*C*(U+1)*R≤N*(C*D)*(U+1)^3 := by
  have hp:=Nat.mul_le_mul_left N h
  simpa only [Nat.mul_assoc] using hp

theorem start_cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (player : Bool) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (U : ℕ) (hN : N≤U) (hU : 1≤U)
    (hml : p.parameters.root.polynomial.length≤4) (hm : HasHeight p.parameters.root.polynomial U)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] U)
    (hl : ∀ j,HasHeight (p.rows.read j).length U)
    (hmean : ∀ j,PlayerSpecificAlgebraicReduction.Reduced p.parameters.root.polynomial (PlayerSpecificInitialLineageBound.means p player j) ∧
      HasHeight (PlayerSpecificInitialLineageBound.means p player j) U) :
    (PlayerSpecificAlgebraicStateExecution.start RationalCostModel.schoolbook p player).2≤(N+1)*startCoefficient*(U+1)^3 := by
  have hm0 : p.parameters.root.polynomial≠[] := by intro h; exact hc.irreducible.ne_zero (by rw [h]; rfl)
  have hcost:=PlayerSpecificAlgebraicStartCost.cost RationalCostModel.schoolbook p player U hN hU hc.normalized hm0 hml hm he hc.interval
    hl (fun j => (hmean j).2) (fun j => by have h:=(hc.lengths j).2; omega) (fun j => by have h:=(hmean j).1.2; omega)
  exact hcost.trans (multiply_profile (N+1) (2*PlayerSpecificAlgebraicComparisonExecution.coefficient+603) U _ _
    (PlayerSpecificResourceCostProfile.cubic _ U))

theorem frame_cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (U : ℕ)
    (hs : PlayerSpecificFiniteResourceSourceCost.StateFits p x U s) (hN : N≤U) (hU : 1≤U)
    (H fuel blocks visits : ℕ) (hH : H≤U) (hf : fuel≤U) (hb : blocks≤U) (hv : visits≤U)
    (hml : p.parameters.root.polynomial.length≤4) (hm : HasHeight p.parameters.root.polynomial U)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] U)
    (hl : ∀ j,HasHeight (p.rows.read j).length U) :
    PlayerSpecificFiniteResourceExecution.frame RationalCostModel.schoolbook p H fuel blocks visits s≤frameCoefficient*(U+1)^3 := by
  have hcost:=PlayerSpecificResourceLoopFrameCost.cost RationalCostModel.schoolbook p s H fuel blocks visits U hN
    ((PlayerSpecificResourceStepCost.active_length p s x hs.1).trans hN) hH hf hb hv hU hm he hml hl hs.2
      (fun j => by have h:=(hc.lengths j).2; omega) (fun j => by have h:=(hs.1.reduced j).2; omega)
  exact hcost.trans (PlayerSpecificResourceCostProfile.cubic 1000 U)

end Blotto.PlayerSpecificResourceEntryPriceProfile
