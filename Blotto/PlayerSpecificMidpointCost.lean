import Blotto.PlayerSpecificMidpointPrimitiveCost
import Blotto.DyadicMidpointAssemblyCost

/-! The complete executing native midpoint has a polynomial source
price with no supplied primitive, width, decoding or metadata oracle. -/
namespace Blotto.PlayerSpecificMidpointCost
open PlayerSpecificRationalTrace PlayerSpecificPolynomialHeights
set_option autoImplicit false
set_option maxHeartbeats 2500000

def width (K : ℕ) : ℕ := PlayerSpecificBalancedPayloadBounds.width (2*K+2)

theorem cost (model : RationalCostModel) (K : ℕ) (bits : Fin K → Bool) :
    (PlayerSpecificMidpointExecution.run model K bits).2≤2000*(K+1)*model.rat (width K) := by
  let S:=2*K+2
  let W:=width K
  let ix:=PlayerSpecificBalancedPayloadExecution.run model (Array.ofFn bits) 0 K
  let denominator:=Nat.shiftLeft 1 (K+1)
  let q:ℚ:=(ix.1:ℚ)
  let d:ℚ:=(denominator:ℚ)
  have hW : 32≤W := by dsimp [W,width,PlayerSpecificBalancedPayloadBounds.width]; omega
  have hWK : K+2≤W := by dsimp [W,width,PlayerSpecificBalancedPayloadBounds.width]; omega
  have hHW : 1+2*(2*K+8)≤W := by dsimp [W,width,PlayerSpecificBalancedPayloadBounds.width]; omega
  have hden : denominator<2^(K+2) := by
    change (1:ℕ) <<< (K+1)<2^(K+2)
    rw [Nat.shiftLeft_eq,Nat.one_mul,show K+2=(K+1)+1 by omega,pow_succ]
    have hp:=Nat.two_pow_pos (K+1)
    omega
  have hdenW : binaryWordWidth denominator≤K+2 := binaryWordWidth_le_of_lt_pow (by omega) hden
  have hixW : binaryWordWidth ix.1≤K+1 := PlayerSpecificBalancedPayloadBounds.result_width model (Array.ofFn bits) 0 K K (Nat.le_refl _)
  have hiq : RationalHeight q (K+2) := DyadicMidpointAssembly.nat_height ix.1 (K+2) (by omega)
    ((PlayerSpecificBalancedPayloadExecution.bounds model (Array.ofFn bits) 0 K).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hdq : RationalHeight d (K+2) := DyadicMidpointAssembly.nat_height denominator (K+2) (by omega) hden
  have h2 : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hdoubled : RationalHeight (q*2) (K+4) := (hiq.mul h2).mono (by omega)
  have hnum : RationalHeight (q*2+1) (K+6) := (hdoubled.add one_height).mono (by omega)
  have hresult : RationalHeight ((q*2+1)/d) (2*K+8) := (hnum.div hdq).mono (by omega)
  have hbuffer:=PlayerSpecificMidpointPrimitiveCost.buffer_cost model K bits W (by omega) hW
  have hdecode:=PlayerSpecificBalancedPayloadCost.cost model (Array.ofFn bits) S (by simp only [Array.size_ofFn]; dsimp [S]; omega)
    0 K (by dsimp [S]; omega)
  have hnodes : PlayerSpecificBalancedPayloadCost.nodes K≤2*K+1 := by unfold PlayerSpecificBalancedPayloadCost.nodes; split <;> omega
  have hdecode' : ix.2≤(2*K+1)*400*model.rat W := hdecode.trans
    (Nat.mul_le_mul_right (model.rat W) (Nat.mul_le_mul_right 400 hnodes))
  have hKWord:=PlayerSpecificBalancedPayloadBounds.small_word K S (by dsimp [S]; omega)
  have hOne:=PlayerSpecificBalancedPayloadBounds.small_word 1 S (by dsimp [S]; omega)
  have hExp:=PlayerSpecificBalancedPayloadBounds.small_word (K+1) S (by dsimp [S]; omega)
  have hDenWord : binaryWordWidth denominator≤S+1 := hdenW.trans (by dsimp [S]; omega)
  have hexponent:=PlayerSpecificBalancedPayloadBounds.binary_cost model (fun a b => a+b) K 1 S hKWord hOne hExp
  have hdenominator:=PlayerSpecificBalancedPayloadBounds.binary_cost model Nat.shiftLeft 1 (K+1) S hOne hExp hDenWord
  have hcastI:=PlayerSpecificMidpointPrimitiveCost.integer_cost model ix.1 (K+2) W hiq (hixW.trans (by omega)) (by omega) hW
  have hcastD:=PlayerSpecificMidpointPrimitiveCost.integer_cost model denominator (K+2) W hdq (hdenW.trans hWK) (by omega) hW
  have hdouble:=PlayerSpecificMidpointPrimitiveCost.scalar_cost model .multiply q 2 (K+2) W hiq (h2.mono (by omega))
    (by dsimp [W,width,PlayerSpecificBalancedPayloadBounds.width]; omega)
  have hadded:=PlayerSpecificMidpointPrimitiveCost.scalar_cost model .add (q*2) 1 (K+4) W hdoubled (one_height.mono (by omega))
    (by dsimp [W,width,PlayerSpecificBalancedPayloadBounds.width]; omega)
  have hdivided:=PlayerSpecificMidpointPrimitiveCost.scalar_cost model .divide (q*2+1) d (K+6) W hnum (hdq.mono (by omega))
    (by dsimp [W,width,PlayerSpecificBalancedPayloadBounds.width]; omega)
  have hframe:=PlayerSpecificMidpointPrimitiveCost.frame_cost model K ix.1 denominator ((q*2+1)/d) (2*K+8) W hresult
    ((control_width K).trans (by omega)) (hixW.trans (by omega)) (hdenW.trans hWK) hHW hW
  change (PlayerSpecificMidpointExecution.buffer model K bits).2+ix.2+
    (PlayerSpecificNaturalExecution.binary model (fun a b => a+b) K 1).2+
    (PlayerSpecificNaturalExecution.binary model Nat.shiftLeft 1 (K+1)).2+
    (PlayerSpecificMidpointExecution.integer model ix.1).2+(PlayerSpecificMidpointExecution.integer model denominator).2+
    price model (scalar .multiply q 2).2+price model (scalar .add (q*2) 1).2+
    price model (scalar .divide (q*2+1) d).2+
      PlayerSpecificMidpointExecution.frame model K ix.1 denominator ((q*2+1)/d)≤_
  change _≤64*model.rat W at hexponent hdenominator
  nlinarith only [hbuffer,hdecode',hexponent,hdenominator,hcastI,hcastD,hdouble,hadded,hdivided,hframe]

theorem polynomial_profile (C D K : ℕ) :
    C*(K+1)*((D*(K+1))*(D*(K+1))+D*(K+1))≤C*(D*D+D)*(K+1)^3 :=
  PlayerSpecificAlgebraicPairCost.cubic_profile C D (K+1) (by omega)

theorem polynomial_cost (K : ℕ) (bits : Fin K → Bool) :
    (PlayerSpecificMidpointExecution.run RationalCostModel.schoolbook K bits).2≤
      (2000*(192*192+192))*(K+1)^3 := by
  have hc:=cost RationalCostModel.schoolbook K bits
  have hw : width K≤192*(K+1) := by dsimp [width,PlayerSpecificBalancedPayloadBounds.width]; omega
  have hp:=hc.trans (Nat.mul_le_mul_left (2000*(K+1)) (RationalCostModel.schoolbook.monotone hw))
  exact hp.trans (polynomial_profile 2000 192 K)

end Blotto.PlayerSpecificMidpointCost
