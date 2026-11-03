import Blotto.PlayerSpecificSturmChainCost

/-! Original-input price of the complete cached signed-remainder sequence,
including trims, derivative, recursive frames and enclosing returned list. -/
namespace Blotto.PlayerSpecificSturmRunCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificSturmExecution PlayerSpecificSquarefreeHeights
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem run_cost (model : RationalCostModel) (p : Data) (H : ℕ)
    (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    price model (run p).2≤2000000000*model.rat (PlayerSpecificGCDTraceCost.capWidth (5*(H+1))) := by
  let first := PlayerSpecificDenseExecution.trim p
  let differentiated := PlayerSpecificDenseExecution.derivative first.1
  let second := PlayerSpecificDenseExecution.trim differentiated.1
  let T := 5*(H+1)
  let W := PlayerSpecificGCDTraceCost.capWidth T
  have hfirstH : HasHeight first.1 H := by rw [PlayerSpecificDenseExecution.trim_value]; exact trim_height hp
  have hfirstl : first.1.length≤4 := by rw [PlayerSpecificDenseExecution.trim_value]; exact (trim_length p).trans hlen
  have hdiffH : HasHeight differentiated.1 T := by
    rw [PlayerSpecificDenseExecution.derivative_value]
    exact derivative_height_four first.1 H hfirstH hfirstl
  have hdiffL : differentiated.1.length≤4 := by rw [PlayerSpecificDenseExecution.derivative_value]; exact (derivative_length _).trans hfirstl
  have hsecondH : HasHeight second.1 T := by rw [PlayerSpecificDenseExecution.trim_value]; exact trim_height hdiffH
  have hsecondL : second.1.length≤4 := by rw [PlayerSpecificDenseExecution.trim_value]; exact (trim_length _).trans hdiffL
  have hT : 1≤T := by dsimp only [T]; omega
  have hHT : H≤T := by dsimp only [T]; omega
  have hcap := PlayerSpecificEuclideanBudget.width_cap second.1.length T hsecondL
  have hwT : 40*T+64≤W := (PlayerSpecificEuclideanBudget.dense_width 0 T).trans (PlayerSpecificEuclideanBudget.width_cap 0 T (by omega))
  have hwH : 40*H+64≤W := (by omega : 40*H+64≤40*T+64).trans hwT
  have hW : 32≤W := (PlayerSpecificEuclideanBudget.width_large 0 T).trans (PlayerSpecificEuclideanBudget.width_cap 0 T (by omega))
  have ht := PlayerSpecificDenseOperationCost.trim_cost model p H 4 hp hlen
  have hd := PlayerSpecificDenseOperationCost.derivative_cost model first.1 H 4 hfirstH hfirstl
  have hs := PlayerSpecificDenseOperationCost.trim_cost model differentiated.1 T 4 hdiffH hdiffL
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at ht hd hs
  have htp:=ht.trans (Nat.mul_le_mul_left 375000 (model.monotone hwH))
  have hdp:=hd.trans (Nat.mul_le_mul_left 375000 (model.monotone hwH))
  have hsp:=hs.trans (Nat.mul_le_mul_left 375000 (model.monotone hwT))
  have hc0:=PlayerSpecificMonicDivisionBudget.control_cost model 0 W (by omega) (by omega)
  have hcf:=PlayerSpecificMonicDivisionBudget.control_cost model second.1.length W hsecondL (by omega)
  rw [run]
  split
  · have hempty := PlayerSpecificSturmCopyCost.copyRows_cost model [] H W (by intro row hr; cases hr)
      (by decide) (by omega) hW
    simp only [price_append]
    nlinarith
  · let rest := chain second.1.length first.1 second.1
    let result := first.1::rest.1
    have hc:=PlayerSpecificSturmChainCost.chain_cost model second.1.length first.1 second.1 T
      (mono hfirstH hHT) hsecondH hT hfirstl hsecondL hsecondL
    have hcp:=hc.trans (Nat.mul_le_mul_left (200000000*(second.1.length+1)) (model.monotone hcap))
    have hfactor:=Nat.mul_le_mul_right (model.rat W)
      (show 200000000*(second.1.length+1)≤1000000000 by omega)
    have hchain : price model rest.2≤1000000000*model.rat W := hcp.trans hfactor
    have hrows : ∀ row∈result,HasHeight row (PlayerSpecificEuclideanBudget.postHeight T) ∧ row.length≤4 := by
      intro row hr
      rcases List.mem_cons.mp hr with he | ht
      · subst row
        exact ⟨mono hfirstH (hHT.trans (PlayerSpecificEuclideanBudget.post_ge T)),hfirstl⟩
      · have hb:=chain_bounds second.1.length first.1 second.1 T (mono hfirstH hHT) hsecondH hT hfirstl hsecondL hsecondL row ht
        have hm:=Nat.mul_le_mul_left PlayerSpecificExtendedGCDHeights.linearConstant
          (show T+1≤PlayerSpecificEuclideanBudget.step T+1 from Nat.add_le_add_right (PlayerSpecificEuclideanBudget.step_ge T) 1)
        exact ⟨mono hb.1 (hm.trans (PlayerSpecificEuclideanBudget.tail_height T)),hb.2⟩
    have hrl : result.length≤5 := by
      have hnorm : PlayerSpecificPolynomialNormalization.Normalized second.1 := by
        rw [PlayerSpecificDenseExecution.trim_value]
        exact PlayerSpecificPolynomialNormalization.trim_normalized _
      have hrest : rest.1.length≤second.1.length := by
        rw [chain_value]
        exact PlayerSpecificSturmSequence.length_bound _ _ _ hnorm
      change (first.1::rest.1).length≤5
      simp only [List.length_cons]
      omega
    have hcopy:=PlayerSpecificSturmCopyCost.copyRows_cost model result (PlayerSpecificEuclideanBudget.postHeight T) W
      hrows hrl ((PlayerSpecificEuclideanBudget.copy_width 0 T).trans (PlayerSpecificEuclideanBudget.width_cap 0 T (by omega))) hW
    change price model (first.2++differentiated.2++second.2++rest.2++copyRows result++[.control second.1.length])≤_
    simp only [price_append]
    nlinarith

end Blotto.PlayerSpecificSturmRunCost
