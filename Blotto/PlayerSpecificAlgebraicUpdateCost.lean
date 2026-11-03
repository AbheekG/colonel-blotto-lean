import Blotto.PlayerSpecificAlgebraicStartCost

/-! The actual two-coordinate writes, local active tests, retained tail
and complete before/after array caller frames have a polynomial price. -/
namespace Blotto.PlayerSpecificAlgebraicUpdateCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicResourceState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem profile (C R S : ℕ) :
    3*(2*C+153)*(S+1)*R+150*(3*S+1)*R+150*(2*S+3)*R≤(6*C+3000)*(S+1)*R := by
  nlinarith only [Nat.zero_le (S*R)]

theorem cost {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (i j : Fin N) (tail : List (Fin N)) (a b : Data)
    (S : ℕ) (hN : N≤S) (hactive : s.active.length≤S) (htail : tail.length+2≤S)
    (hm : Normalized p.parameters.root.polynomial) (hm0 : p.parameters.root.polynomial≠[])
    (hml : p.parameters.root.polynomial.length≤4)
    (hmH : HasHeight p.parameters.root.polynomial S) (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] S)
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi)
    (hl : ∀ k,HasHeight (p.rows.read k).length S) (hr : ∀ k,HasHeight (s.data.read k) S)
    (hll : ∀ k,(p.rows.read k).length.length≤3) (hrl : ∀ k,(s.data.read k).length≤3)
    (haH : HasHeight a S) (hbH : HasHeight b S) (hal : a.length≤3) (hbl : b.length≤3) :
    (PlayerSpecificAlgebraicStateExecution.update model p s i j tail a b).2≤
      (6*PlayerSpecificAlgebraicComparisonExecution.coefficient+3000)*(S+1)*
        model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let data:=(s.data.write i a).write j b
  let lengths:=PlayerSpecificAlgebraicStateExecution.lengths p
  let result:=(PlayerSpecificAlgebraicStateExecution.update model p s i j tail a b).1
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hS : 1≤S := by omega
  have hdH : ∀ k,HasHeight (data.read k) S := by
    intro k
    simp only [data,FixedArrayTable.read_write]
    split
    · exact hbH
    · split
      · exact haH
      · exact hr k
  have hdl : ∀ k,(data.read k).length≤3 := by
    intro k
    simp only [data,FixedArrayTable.read_write]
    split
    · exact hbl
    · split
      · exact hal
      · exact hrl k
  have hlH : ∀ k,HasHeight (lengths.read k) S := by
    intro k
    change HasHeight ((FixedArrayTable.ofFn (fun l => (p.rows.read l).length)).read k) S
    rw [FixedArrayTable.read_ofFn]
    exact hl k
  have hlen : ∀ k,(lengths.read k).length≤3 := by
    intro k
    change ((FixedArrayTable.ofFn (fun l => (p.rows.read l).length)).read k).length≤3
    rw [FixedArrayTable.read_ofFn]
    exact hll k
  have hfilter:=PlayerSpecificAlgebraicActiveListCost.cost model p.parameters.root lengths data S hN hS hm hm0 hml hmH he hv
    hlH hdH hlen hdl [i,j] (by simp; omega)
  have hresult : result.active.length≤S := by
    have hlen:=PlayerSpecificAlgebraicActiveListExecution.length model p.parameters.root lengths data [i,j]
    change ((PlayerSpecificAlgebraicActiveListExecution.run model p.parameters.root lengths data [i,j]).1++tail).length≤S
    simp only [List.length_append]
    simp only [List.length_cons,List.length_nil] at hlen
    omega
  have hresultH : ∀ k,HasHeight (result.data.read k) S := hdH
  have hresultl : ∀ k,(result.data.read k).length≤3 := hdl
  have hframe1:=PlayerSpecificAlgebraicStateFrameCost.cost model p s tail S hN hactive (by omega)
    hmH he hml hl hr hll hrl
  have hframe2:=PlayerSpecificAlgebraicStateFrameCost.cost model p result [i,j] S hN hresult (by simp; omega)
    hmH he hml hl hresultH hll hresultl
  have hf1 : price model (PlayerSpecificAlgebraicStateExecution.frame p s tail)≤150*(3*S+1)*model.rat W := by
    apply hframe1.trans
    apply Nat.mul_le_mul_right (model.rat W)
    apply Nat.mul_le_mul_left 150
    omega
  have hf2 : price model (PlayerSpecificAlgebraicStateExecution.frame p result [i,j])≤150*(2*S+3)*model.rat W := by
    apply hframe2.trans
    apply Nat.mul_le_mul_right (model.rat W)
    apply Nat.mul_le_mul_left 150
    simp only [List.length_cons,List.length_nil]
    omega
  have hsum:=Nat.add_le_add (Nat.add_le_add hfilter hf1) hf2
  simp only [List.length_cons,List.length_nil] at hsum
  exact hsum.trans (profile PlayerSpecificAlgebraicComparisonExecution.coefficient (model.rat W) S)

end Blotto.PlayerSpecificAlgebraicUpdateCost
