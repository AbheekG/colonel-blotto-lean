import Blotto.PlayerSpecificResourceStepSizes

/-! Complete prices of an actually reached request, coin and selected
advance at one derived common envelope. All operands come from the live
valid state and cached pair; no per-step cost or height oracle is used. -/
namespace Blotto.PlayerSpecificResourceStepCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

def requestCoefficient : ℕ := PlayerSpecificAlgebraicPairCost.polynomialCoefficient+
  450*PlayerSpecificResourceCostProfile.rationalCoefficient
def advanceCoefficient : ℕ := (6*PlayerSpecificAlgebraicComparisonExecution.coefficient+3000)*
  PlayerSpecificResourceCostProfile.rationalCoefficient

theorem active_length {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (x : ℝ) (hs : Valid p x s) :
    s.active.length≤N := by simpa only [Fintype.card_fin] using hs.nodup.length_le_card

theorem request_cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (hs : Valid p x s) (U : ℕ) (hN : N≤U)
    (hml : p.parameters.root.polynomial.length≤4) (hm : HasHeight p.parameters.root.polynomial U)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] U)
    (hl : ∀ j,HasHeight (p.rows.read j).length U) (hr : ∀ j,HasHeight (s.data.read j) U) :
    (PlayerSpecificAlgebraicRequestExecution.request RationalCostModel.schoolbook p s).2≤
      requestCoefficient*(PlayerSpecificResourceStepSizes.height U+1)^3 := by
  let V:=PlayerSpecificResourceStepSizes.height U
  have hUV : U≤V := (PlayerSpecificResourceStepSizes.large U 0 (Nat.zero_le _)).1
  have hm0 : p.parameters.root.polynomial≠[] := by intro h; exact hc.irreducible.ne_zero (by rw [h]; rfl)
  have hcost:=PlayerSpecificAlgebraicRequestCost.cost p s V (hN.trans hUV)
    ((active_length p s x hs).trans (hN.trans hUV)) hc.normalized hm0 hml (mono hm hUV) (mono he hUV) hc.interval
      (fun j => mono (hl j) hUV) (fun j => mono (hr j) hUV) hc.lengths hs.reduced
  exact hcost.trans (PlayerSpecificResourceCostProfile.request_profile V)

theorem coin_cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (f : Frame N)
    (hf : request RationalCostModel.schoolbook p s=some f) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (hs : Valid p x s) (U H : ℕ) (hH : H≤U)
    (hml : p.parameters.root.polynomial.length≤4) (hm : HasHeight p.parameters.root.polynomial U)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] U)
    (hl : ∀ j,HasHeight (p.rows.read j).length U) (hr : ∀ j,HasHeight (s.data.read j) U) (bits : Fin H → Bool) :
    (PlayerSpecificAlgebraicCoinExecution.run RationalCostModel.schoolbook p.parameters.root f.pair.probability H bits).2≤
      PlayerSpecificAlgebraicCoinCost.polynomialCoefficient*(PlayerSpecificResourceStepSizes.height U+1)^3 := by
  let Q:=PlayerSpecificAlgebraicPairHeights.probabilityHeight U
  have hQU : U≤Q := by
    have h:=PlayerSpecificAlgebraicHeightEnvelope.large (2*PlayerSpecificAlgebraicPairHeights.resourceHeight U+1)
    change U≤PlayerSpecificAlgebraicHeightEnvelope.step (2*PlayerSpecificAlgebraicPairHeights.resourceHeight U+1)
    unfold PlayerSpecificAlgebraicPairHeights.resourceHeight at h ⊢
    omega
  have hm0 : p.parameters.root.polynomial≠[] := by intro h; exact hc.irreducible.ne_zero (by rw [h]; rfl)
  have hsize:=PlayerSpecificResourceStepSizes.requested p s f hf x hc hs U hml hm hl hr
  have hcost:=PlayerSpecificAlgebraicCoinCost.cost p.parameters.root f.pair.probability Q H bits hc.normalized hm0 hml
    (mono hm hQU) (mono he hQU) hc.interval hsize.2.1 hsize.1
  have hp : (Q+H+3)^3≤(PlayerSpecificResourceStepSizes.height U+1)^3 :=
    Nat.pow_le_pow_left (PlayerSpecificResourceStepSizes.large U H hH).2.2.1 3
  exact hcost.trans (Nat.mul_le_mul_left _ hp)

theorem advance_cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (f : Frame N)
    (hf : request RationalCostModel.schoolbook p s=some f) (upper : Bool) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (hs : Valid p x s) (U : ℕ) (hN : N≤U)
    (hml : p.parameters.root.polynomial.length≤4) (hm : HasHeight p.parameters.root.polynomial U)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] U)
    (hl : ∀ j,HasHeight (p.rows.read j).length U) (hr : ∀ j,HasHeight (s.data.read j) U) :
    (PlayerSpecificAlgebraicRequestExecution.advance RationalCostModel.schoolbook p s f upper).2≤
      advanceCoefficient*(PlayerSpecificResourceStepSizes.height U+1)^3 := by
  let V:=PlayerSpecificResourceStepSizes.height U
  have hlarge:=PlayerSpecificResourceStepSizes.large U 0 (Nat.zero_le _)
  have hUV : U≤V := hlarge.1
  have hGV : PlayerSpecificAlgebraicPairHeights.resourceHeight U≤V := hlarge.2.1
  have hm0 : p.parameters.root.polynomial≠[] := by intro h; exact hc.irreducible.ne_zero (by rw [h]; rfl)
  have hsize:=(PlayerSpecificResourceStepSizes.requested p s f hf x hc hs U hml hm hl hr).2.2 upper
  have hshape:=(fields RationalCostModel.schoolbook p s f hf).1
  have hactive : s.active.length≤V := (active_length p s x hs).trans (hN.trans hUV)
  have htail : f.tail.length+2≤V := by rw [hshape,List.length_cons,List.length_cons] at hactive; omega
  have hll : ∀ j,(p.rows.read j).length.length≤3 := by intro j; have hh:=(hc.lengths j).2; omega
  have hrl : ∀ j,(s.data.read j).length≤3 := by intro j; have hh:=(hs.reduced j).2; omega
  have hal : (if upper then f.pair.upperA else f.pair.lowerA).length≤3 := by have hh:=hsize.1.1.2; omega
  have hbl : (if upper then f.pair.upperB else f.pair.lowerB).length≤3 := by have hh:=hsize.2.1.2; omega
  have hcost:=PlayerSpecificAlgebraicUpdateCost.cost RationalCostModel.schoolbook p s f.first f.second f.tail
    (if upper then f.pair.upperA else f.pair.lowerA) (if upper then f.pair.upperB else f.pair.lowerB)
      V (hN.trans hUV) hactive htail hc.normalized hm0 hml (mono hm hUV) (mono he hUV) hc.interval
        (fun j => mono (hl j) hUV) (fun j => mono (hr j) hUV) hll hrl (mono hsize.1.2 hGV) (mono hsize.2.2 hGV) hal hbl
  exact hcost.trans (PlayerSpecificResourceCostProfile.cubic _ V)

end Blotto.PlayerSpecificResourceStepCost
