import Blotto.PlayerSpecificResourceStepCost

/-! Complete aggregate source price of the actual finite resource loop.
Reached-state certificates are derived separately from original inputs;
the executing loop accepts no size, arithmetic or cost oracle. -/
namespace Blotto.PlayerSpecificFiniteResourceSourceCost
open PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def StateFits {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ) (U : ℕ) (s : State N) : Prop :=
  Valid p x s ∧ ∀ j,HasHeight (s.data.read j) U
def frameCoefficient : ℕ := 1000*PlayerSpecificResourceCostProfile.rationalCoefficient
def coefficient : ℕ := PlayerSpecificResourceStepCost.requestCoefficient+PlayerSpecificAlgebraicCoinCost.polynomialCoefficient+
  PlayerSpecificResourceStepCost.advanceCoefficient+frameCoefficient

theorem frame_cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (x : ℝ) (U : ℕ)
    (hs : StateFits p x U s) (hN : N≤U) (H fuel blocks visits : ℕ)
    (hH : H≤U) (hf : fuel≤U) (hb : blocks≤U) (hv : visits≤U)
    (hml : p.parameters.root.polynomial.length≤4) (hm : HasHeight p.parameters.root.polynomial U)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] U)
    (hl : ∀ j,HasHeight (p.rows.read j).length U)
    (hlred : ∀ j,PlayerSpecificAlgebraicReduction.Reduced p.parameters.root.polynomial (p.rows.read j).length) :
    PlayerSpecificFiniteResourceExecution.frame RationalCostModel.schoolbook p H fuel blocks visits s≤
      frameCoefficient*(PlayerSpecificResourceStepSizes.height U+1)^3 := by
  let V:=PlayerSpecificResourceStepSizes.height U
  have hlarge:=PlayerSpecificResourceStepSizes.large U 0 (Nat.zero_le _)
  have hUV : U≤V := hlarge.1
  have hactive : s.active.length≤V := (PlayerSpecificResourceStepCost.active_length p s x hs.1).trans (hN.trans hUV)
  have hll : ∀ j,(p.rows.read j).length.length≤3 := by intro j; have h:=(hlred j).2; omega
  have hrl : ∀ j,(s.data.read j).length≤3 := by intro j; have h:=(hs.1.reduced j).2; omega
  have hc:=PlayerSpecificResourceLoopFrameCost.cost RationalCostModel.schoolbook p s H fuel blocks visits V
    (hN.trans hUV) hactive (hH.trans hUV) (hf.trans hUV) (hb.trans hUV) (hv.trans hUV) hlarge.2.2.2
      (mono hm hUV) (mono he hUV) hml (fun j => mono (hl j) hUV) (fun j => mono (hs.2 j) hUV) hll hrl
  exact hc.trans (PlayerSpecificResourceCostProfile.cubic 1000 V)

theorem stop_profile (R B A F n t : ℕ) : R*t+F*t≤(n+2)*(R+B+A+F)*t := by
  nlinarith only [Nat.zero_le (n*(R+B+A+F)*t)]

theorem step_profile (R B A F n t : ℕ) :
    R*t+B*t+A*t+(n+1)*(R+B+A+F)*t+F*t=(n+2)*(R+B+A+F)*t := by ring

theorem cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (U : ℕ) (hN : N≤U)
    (hml : p.parameters.root.polynomial.length≤4) (hm : HasHeight p.parameters.root.polynomial U)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] U)
    (hl : ∀ j,HasHeight (p.rows.read j).length U) (H : ℕ) (hH : H≤U) :
    ∀ (fuel : ℕ) (s : State N) (blocks : List (Fin H → Bool)),fuel≤U → blocks.length≤U →
      PlayerSpecificResourceVisitedStates.All RationalCostModel.schoolbook p (StateFits p x U) fuel s →
      (PlayerSpecificFiniteResourceExecution.run RationalCostModel.schoolbook p H fuel s blocks).2≤
        (fuel+1)*coefficient*(PlayerSpecificResourceStepSizes.height U+1)^3 := by
  let model:=RationalCostModel.schoolbook
  let V:=PlayerSpecificResourceStepSizes.height U
  let t:=(V+1)^3
  intro fuel
  induction fuel with
  | zero =>
    intro s blocks _ hb hAll
    have hs:=PlayerSpecificResourceVisitedStates.head model p (StateFits p x U) 0 s hAll
    have hf:=frame_cost p s x U hs hN H 0 blocks.length 0 hH (Nat.zero_le _) hb (Nat.zero_le _) hml hm he hl hc.lengths
    have hcoeff : frameCoefficient≤coefficient := by unfold coefficient; omega
    exact hf.trans (Nat.mul_le_mul_right t hcoeff)
  | succ fuel ih =>
    intro s blocks hf hb hAll
    have hs:=PlayerSpecificResourceVisitedStates.head model p (StateFits p x U) (fuel+1) s hAll
    have hrequest:=PlayerSpecificResourceStepCost.request_cost p s x hc hs.1 U hN hml hm he hl hs.2
    simp only [PlayerSpecificFiniteResourceExecution.run,PlayerSpecificAlgebraicRequestExecution.request_value]
    cases hreq : PlayerSpecificAlgebraicResourceRequest.request model p s with
    | none =>
      have hframe:=frame_cost p s x U hs hN H (fuel+1) blocks.length 0 hH hf hb (Nat.zero_le _) hml hm he hl hc.lengths
      have hsum:=Nat.add_le_add hrequest hframe
      exact hsum.trans (stop_profile PlayerSpecificResourceStepCost.requestCoefficient PlayerSpecificAlgebraicCoinCost.polynomialCoefficient
        PlayerSpecificResourceStepCost.advanceCoefficient frameCoefficient fuel t)
    | some f =>
      let coin:=PlayerSpecificAlgebraicCoinExecution.run model p.parameters.root f.pair.probability H (blocks.headD (fun _ => false))
      let next:=PlayerSpecificAlgebraicRequestExecution.advance model p s f coin.1
      let tail:=PlayerSpecificFiniteResourceExecution.run model p H fuel next.1 blocks.tail
      have hnext : PlayerSpecificResourceVisitedStates.All model p (StateFits p x U) fuel next.1 := by
        change PlayerSpecificResourceVisitedStates.All model p (StateFits p x U) fuel
          (PlayerSpecificAlgebraicRequestExecution.advance model p s f coin.1).1
        rw [PlayerSpecificAlgebraicRequestExecution.advance_value]
        exact PlayerSpecificResourceVisitedStates.next model p (StateFits p x U) fuel s hAll f hreq coin.1
      have hblocks : blocks.tail.length≤U := by rw [List.length_tail]; omega
      have htail:=ih next.1 blocks.tail (by omega) hblocks hnext
      have hout:=PlayerSpecificResourceVisitedStates.measured_output model p (StateFits p x U) H fuel next.1 hnext blocks.tail
      have hvisits : tail.1.2≤fuel := PlayerSpecificFiniteResourceExecution.visits_le model p H fuel next.1 blocks.tail
      have hcoin:=PlayerSpecificResourceStepCost.coin_cost p s f hreq x hc hs.1 U H hH hml hm he hl hs.2 (blocks.headD (fun _ => false))
      have hadvance:=PlayerSpecificResourceStepCost.advance_cost p s f hreq coin.1 x hc hs.1 U hN hml hm he hl hs.2
      have hframe:=frame_cost p tail.1.1 x U hout hN H (fuel+1) blocks.length (tail.1.2+1) hH hf hb (by omega) hml hm he hl hc.lengths
      have hsum:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hrequest hcoin) hadvance) htail) hframe
      apply hsum.trans_eq
      exact step_profile PlayerSpecificResourceStepCost.requestCoefficient PlayerSpecificAlgebraicCoinCost.polynomialCoefficient
        PlayerSpecificResourceStepCost.advanceCoefficient frameCoefficient fuel t

end Blotto.PlayerSpecificFiniteResourceSourceCost
