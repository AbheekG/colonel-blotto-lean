import Blotto.PlayerSpecificAlgebraicRequestExecution

/-! Every actual request has a polynomial price from its computed rows,
including stopped requests and all enclosing state/index copies. -/
namespace Blotto.PlayerSpecificAlgebraicRequestCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (S : ℕ) (hN : N≤S) (hactive : s.active.length≤S)
    (hm : Normalized p.parameters.root.polynomial) (hm0 : p.parameters.root.polynomial≠[])
    (hml : p.parameters.root.polynomial.length≤4)
    (hmH : HasHeight p.parameters.root.polynomial S) (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] S)
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi)
    (hl : ∀ k,HasHeight (p.rows.read k).length S) (hr : ∀ k,HasHeight (s.data.read k) S)
    (hlred : ∀ k,Reduced p.parameters.root.polynomial (p.rows.read k).length)
    (hrred : ∀ k,Reduced p.parameters.root.polynomial (s.data.read k)) :
    (PlayerSpecificAlgebraicRequestExecution.request RationalCostModel.schoolbook p s).2≤
      PlayerSpecificAlgebraicPairCost.polynomialCoefficient*(S+1)^3+
        150*(3*S+1)*RationalCostModel.schoolbook.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let model:=RationalCostModel.schoolbook
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hll : ∀ k,(p.rows.read k).length.length≤3 := by intro k; have hh:=(hlred k).2; omega
  have hrl : ∀ k,(s.data.read k).length≤3 := by intro k; have hh:=(hrred k).2; omega
  have hf : ∀ ids : List (Fin N),ids.length≤S →
      price model (PlayerSpecificAlgebraicStateExecution.frame p s ids)≤150*(3*S+1)*model.rat W := by
    intro ids hids
    have hc:=PlayerSpecificAlgebraicStateFrameCost.cost model p s ids S hN hactive hids hmH he hml hl hr hll hrl
    apply hc.trans
    apply Nat.mul_le_mul_right (model.rat W)
    apply Nat.mul_le_mul_left 150
    omega
  unfold PlayerSpecificAlgebraicRequestExecution.request
  split
  · have hc:=hf [] (by simp)
    exact hc.trans (Nat.le_add_left _ _)
  · have hc:=hf [] (by simp)
    exact hc.trans (Nat.le_add_left _ _)
  · rename_i i j tail hshape
    have ht : tail.length≤S := by rw [hshape,List.length_cons,List.length_cons] at hactive; omega
    have hc:=PlayerSpecificAlgebraicPairCost.polynomial_cost p.parameters.root (p.rows.read i).length (p.rows.read j).length
      (s.data.read i) (s.data.read j) S hm hm0 hml (hlred i) (hlred j) (hrred i) (hrred j) hmH he hv (hl i) (hl j) (hr i) (hr j)
    exact Nat.add_le_add hc (hf tail ht)

end Blotto.PlayerSpecificAlgebraicRequestCost
