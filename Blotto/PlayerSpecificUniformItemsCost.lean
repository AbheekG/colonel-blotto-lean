import Blotto.PlayerSpecificUniformItemsExecution

/-! Complete saturated-coordinate filtering has polynomial source work,
including exact equality, index reads and retained list/caller copies. -/
namespace Blotto.PlayerSpecificUniformItemsCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem frame_cost {N : ℕ} (model : RationalCostModel) (j : Fin N) (ids result : List (Fin N)) (S : ℕ)
    (hN : N≤S) (hi : ids.length≤S) (hr : result.length ≤ ids.length) (hS : 1≤S) :
    price model (PlayerSpecificUniformItemsExecution.frame j ids result)≤
      32*(S+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hw : ∀ word∈[N,j.val,ids.length,result.length,1]++ids.map Fin.val++result.map Fin.val,binaryWordWidth word≤W := by
    intro word hw
    have hsmall : word≤S := by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with ((hw|hw|hw|hw|hw)|hw)|hw
      · omega
      · have hj:=j.isLt; omega
      · omega
      · omega
      · omega
      · obtain ⟨k,_,rfl⟩:=List.mem_map.mp hw
        exact (Nat.le_of_lt k.isLt).trans hN
      · obtain ⟨k,_,rfl⟩:=List.mem_map.mp hw
        exact (Nat.le_of_lt k.isLt).trans hN
    exact (control_width word).trans ((Nat.add_le_add_right hsmall 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model [] ([N,j.val,ids.length,result.length,1]++ids.map Fin.val++result.map Fin.val)
    0 W (by simp) (by simp) hw (by have h:32≤W:=(PlayerSpecificAlgebraicActiveListCost.width_large S).1; omega)
      (PlayerSpecificAlgebraicActiveListCost.width_large S).1
  apply hc.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [List.length_nil,List.length_cons,List.length_append,List.length_map]
  omega

theorem profile (K S R t : ℕ) : K*R+(t+1)*(K+64)*(S+1)*R+32*(S+1)*R≤(t+2)*(K+64)*(S+1)*R := by
  nlinarith only [Nat.zero_le (K*S*R),Nat.zero_le (S*R),Nat.zero_le R]

theorem cost {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (S : ℕ) (hN : N≤S) (hS : 1≤S)
    (hm : Normalized p.parameters.root.polynomial) (hm0 : p.parameters.root.polynomial≠[]) (hml : p.parameters.root.polynomial.length≤4)
    (hmS : HasHeight p.parameters.root.polynomial S)
    (hl : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length ∧ HasHeight (p.rows.read j).length S)
    (hr : ∀ j,Reduced p.parameters.root.polynomial (s.data.read j) ∧ HasHeight (s.data.read j) S) :
    ∀ ids : List (Fin N),ids.length≤S → (PlayerSpecificUniformItemsExecution.run model p s ids).2≤
      (ids.length+1)*(PlayerSpecificAlgebraicEqualityCost.coefficient+64)*(S+1)*
        model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  let K:=PlayerSpecificAlgebraicEqualityCost.coefficient
  intro ids
  induction ids with
  | nil =>
    intro _
    have hc:=PlayerSpecificAlgebraicCallerFrame.cost model [] [N,0,1] 0 W (by simp) (by simp)
      (by intro word hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with hw|hw|hw
          · rw [hw]; exact (control_width N).trans ((Nat.add_le_add_right hN 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
          · rw [hw]; exact (control_width 0).trans (by have h:32≤W:=(PlayerSpecificAlgebraicActiveListCost.width_large S).1; omega)
          · rw [hw]; exact (control_width 1).trans (by have h:32≤W:=(PlayerSpecificAlgebraicActiveListCost.width_large S).1; omega))
      (by have h:32≤W:=(PlayerSpecificAlgebraicActiveListCost.width_large S).1; omega) (PlayerSpecificAlgebraicActiveListCost.width_large S).1
    change price model (PlayerSpecificAlgebraicCallerFrame.run [] [N,0,1])≤_
    apply hc.trans
    simp only [List.length_nil,List.length_cons,Nat.mul_zero,Nat.zero_add,Nat.one_mul]
    apply Nat.mul_le_mul_right (model.rat W)
    change 9≤(K+64)*(S+1)
    have hm:=Nat.mul_le_mul_left (K+64) (show 1≤S+1 by omega)
    omega
  | cons j ids ih =>
    intro hids
    have ht:=ih (by simp only [List.length_cons] at hids; omega)
    have heq:=PlayerSpecificAlgebraicEqualityCost.cost model p.parameters.root.polynomial (s.data.read j) (p.rows.read j).length S
      hm hm0 hml (hr j).1 (hl j).1 hmS (hr j).2 (hl j).2 hS
    let result:=(PlayerSpecificUniformItemsExecution.run model p s (j::ids)).1
    have hresult : result.length≤(j::ids).length := PlayerSpecificUniformItemsExecution.length model p s (j::ids)
    have hf:=frame_cost model j (j::ids) result S hN hids hresult hS
    have hsum:=Nat.add_le_add (Nat.add_le_add heq ht) hf
    change _≤K*model.rat W+(ids.length+1)*(K+64)*(S+1)*model.rat W+32*(S+1)*model.rat W at hsum
    exact hsum.trans (profile K S (model.rat W) ids.length)

end Blotto.PlayerSpecificUniformItemsCost
