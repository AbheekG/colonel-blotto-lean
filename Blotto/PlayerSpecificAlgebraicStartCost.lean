import Blotto.PlayerSpecificAlgebraicStateFrameCost

/-! The actual initial resource array and active filter have a complete
source bound. Every input/returned row and finite index is accounted for. -/
namespace Blotto.PlayerSpecificAlgebraicStartCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicResourceState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem profile (C R N S : ℕ) :
    (N+1)*(2*C+153)*(S+1)*R+150*(3*N+1)*R≤(N+1)*(2*C+603)*(S+1)*R := by
  nlinarith only [Nat.zero_le (N*S*R),Nat.zero_le (S*R)]

theorem cost {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (player : Bool) (S : ℕ) (hN : N≤S) (hS : 1≤S)
    (hm : Normalized p.parameters.root.polynomial) (hm0 : p.parameters.root.polynomial≠[])
    (hml : p.parameters.root.polynomial.length≤4)
    (hmH : HasHeight p.parameters.root.polynomial S) (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] S)
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi)
    (hl : ∀ j,HasHeight (p.rows.read j).length S)
    (hr : ∀ j,HasHeight (PlayerSpecificInitialLineageBound.means p player j) S)
    (hll : ∀ j,(p.rows.read j).length.length≤3)
    (hrl : ∀ j,(PlayerSpecificInitialLineageBound.means p player j).length≤3) :
    (PlayerSpecificAlgebraicStateExecution.start model p player).2≤
      (N+1)*(2*PlayerSpecificAlgebraicComparisonExecution.coefficient+603)*(S+1)*
        model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let data:=FixedArrayTable.ofFn (PlayerSpecificInitialLineageBound.means p player)
  let lengths:=PlayerSpecificAlgebraicStateExecution.lengths p
  let result:=(PlayerSpecificAlgebraicStateExecution.start model p player).1
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hdH : ∀ j,HasHeight (data.read j) S := by intro j; rw [FixedArrayTable.read_ofFn]; exact hr j
  have hdl : ∀ j,(data.read j).length≤3 := by intro j; rw [FixedArrayTable.read_ofFn]; exact hrl j
  have hlH : ∀ j,HasHeight (lengths.read j) S := by
    intro j
    change HasHeight ((FixedArrayTable.ofFn (fun k => (p.rows.read k).length)).read j) S
    rw [FixedArrayTable.read_ofFn]
    exact hl j
  have hlen : ∀ j,(lengths.read j).length≤3 := by
    intro j
    change ((FixedArrayTable.ofFn (fun k => (p.rows.read k).length)).read j).length≤3
    rw [FixedArrayTable.read_ofFn]
    exact hll j
  have hfilter:=PlayerSpecificAlgebraicActiveListCost.cost model p.parameters.root lengths data S hN hS hm hm0 hml hmH he hv
    hlH hdH hlen hdl (List.finRange N) (by simpa only [List.length_finRange] using hN)
  have hactive : result.active.length≤N := by
    change (PlayerSpecificAlgebraicActiveListExecution.run model p.parameters.root lengths data (List.finRange N)).1.length≤N
    simpa only [List.length_finRange] using PlayerSpecificAlgebraicActiveListExecution.length model p.parameters.root lengths data (List.finRange N)
  have hresultH : ∀ j,HasHeight (result.data.read j) S := hdH
  have hresultl : ∀ j,(result.data.read j).length≤3 := hdl
  have hframe:=PlayerSpecificAlgebraicStateFrameCost.cost model p result (List.finRange N) S hN (hactive.trans hN)
    (by simpa only [List.length_finRange] using hN) hmH he hml hl hresultH hll hresultl
  have hf : price model (PlayerSpecificAlgebraicStateExecution.frame p result (List.finRange N))≤150*(3*N+1)*model.rat W := by
    apply hframe.trans
    apply Nat.mul_le_mul_right (model.rat W)
    apply Nat.mul_le_mul_left 150
    simp only [List.length_finRange]
    omega
  have hsum:=Nat.add_le_add hfilter hf
  simp only [List.length_finRange] at hsum
  exact hsum.trans (profile PlayerSpecificAlgebraicComparisonExecution.coefficient (model.rat W) N S)

end Blotto.PlayerSpecificAlgebraicStartCost
