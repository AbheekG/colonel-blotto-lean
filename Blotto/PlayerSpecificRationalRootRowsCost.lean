import Blotto.PlayerSpecificRationalRootRows

/-! Complete bounded-leaf enumeration source price, including complete
copied lists at every option branch and returned frame. -/
namespace Blotto.PlayerSpecificRationalRootRowsCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificIsolationState PlayerSpecificRationalMagnitude
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem copy_cost (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (nodes : List Interval) (hcap : nodes.length≤3) :
    price model (copyRow (PlayerSpecificRationalRootRows.run model p (PlayerSpecificReconstructionCache.run model p).1 nodes).1)≤
      15*model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)) := by
  let result:=(PlayerSpecificRationalRootRows.run model p (PlayerSpecificReconstructionCache.run model p).1 nodes).1
  have hheight : HasHeight result (PlayerSpecificRationalRootHeight.height p) := by
    intro q hq
    exact PlayerSpecificRationalRootHeight.root_height p hp hlen q (PlayerSpecificRationalRootRows.root model p nodes q hq)
  have hlength : result.length≤4 := ((PlayerSpecificRationalRootRows.length model p _ nodes).trans hcap).trans (by decide)
  have hrootH : PlayerSpecificRationalRootHeight.height p≤PlayerSpecificIntegerBudget.height (inputHeight p) := by
    have hseven:=(PlayerSpecificReconstructionCacheBudget.controls p hlen).2.1
    unfold PlayerSpecificRationalRootHeight.height
    omega
  exact PlayerSpecificMonicDivisionBudget.copy_cost model result _ _ hheight hlength
    (PlayerSpecificIntegerBudget.copy_width _ _ hrootH) ((by decide : 6≤32).trans (PlayerSpecificIntegerBudget.width_large _))

theorem run_cost (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (nodes : List Interval) (hcap : nodes.length≤3) (hnode : ∀ node∈nodes,node∈PlayerSpecificRationalRoots.intervals p) :
    (PlayerSpecificRationalRootRows.run model p (PlayerSpecificReconstructionCache.run model p).1 nodes).2≤
      20010000*(nodes.length+1)*(PlayerSpecificIntegerBudget.height (inputHeight p)+1)*
        model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)) := by
  let J:=PlayerSpecificIntegerBudget.height (inputHeight p)
  let W:=PlayerSpecificIntegerBudget.width (inputHeight p)
  let cache:=(PlayerSpecificReconstructionCache.run model p).1
  have hword : cache.word≤model.rat W := (PlayerSpecificReconstructionCacheBudget.source_word model p hlen).trans (model.word_le W)
  induction nodes with
  | nil =>
    change 16*cache.word≤20010000*(0+1)*(J+1)*model.rat W
    nlinarith only [hword]
  | cons node nodes ih =>
    have hnodes : nodes.length≤3 := by simp only [List.length_cons] at hcap; omega
    have htail:=ih hnodes (fun q hq => hnode q (List.mem_cons_of_mem node hq))
    have hhead:=PlayerSpecificReconstructionLeafCost.run_cost model p hlen node (hnode node List.mem_cons_self)
    have hcopy:=copy_cost model p hp hlen (node::nodes) hcap
    rw [PlayerSpecificRationalRootRows.run] at hcopy ⊢
    dsimp only at hcopy ⊢
    simp only [List.length_cons]
    nlinarith only [hhead,htail,hcopy,hword]

end Blotto.PlayerSpecificRationalRootRowsCost
