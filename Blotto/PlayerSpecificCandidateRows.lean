import Blotto.PlayerSpecificCandidateSelection

/-! Actual candidate-list construction with full prefix/returned copies.
Its bounded-depth list recursion covers every retained original root. -/
namespace Blotto.PlayerSpecificCandidateRows
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificIsolationState PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 3000000

def copyRows (rows : List Candidate) : Trace :=
  [.control rows.length]++rows.flatMap PlayerSpecificCandidateSelection.copyCandidate

def run (model : RationalCostModel) (factors residual : Data) : List Interval → List Candidate×ℕ
  | [] => ([],price model (copyRows []))
  | node::nodes =>
    let chosen:=PlayerSpecificCandidateSelection.run model factors residual node
    let rest:=run model factors residual nodes
    let result:=chosen.1::rest.1
    (result,chosen.2+rest.2+price model (copyRows result)+price model (copyRow factors)+
      price model (copyRow residual)+price model [.control (node::nodes).length])

theorem value (model : RationalCostModel) (factors residual : Data) (nodes : List Interval) :
    (run model factors residual nodes).1=nodes.map (select factors residual) := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => simp only [run,PlayerSpecificCandidateSelection.value,ih,List.map_cons]

theorem copy_cost (model : RationalCostModel) (rows : List Candidate) (W : ℕ) (hW : 32≤W)
    (hlen : rows.length≤3)
    (h : ∀ c∈rows,price model (PlayerSpecificCandidateSelection.copyCandidate c)≤81*model.rat W) :
    price model (copyRows rows)≤250*model.rat W := by
  have hs : (rows.map (fun c => price model (PlayerSpecificCandidateSelection.copyCandidate c))).sum≤
      rows.length*(81*model.rat W) := by
    induction rows with
    | nil => simp
    | cons c cs ih =>
      have hc:=h c List.mem_cons_self
      have ht:=ih (by simp only [List.length_cons] at hlen; omega)
        (fun d hd => h d (List.mem_cons_of_mem c hd))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [hc,ht]
  have hctrl:=event_price model W (by omega) (.control rows.length) ((control_width _).trans (by omega))
  change price model [.control rows.length]≤3*model.rat W at hctrl
  have hm:=Nat.mul_le_mul_right (81*model.rat W) hlen
  rw [copyRows,price_append,PlayerSpecificTraversalPrice.price_flatMap]
  nlinarith only [hs,hctrl,hm]

theorem returned_copy (model : RationalCostModel) (factors residual : Data) (nodes : List Interval) (H W : ℕ)
    (hf : HasHeight factors H) (hr : HasHeight residual H) (hrl : residual.length≤4)
    (hn : nodes.length≤3) (hH : 1≤H) (hHW : 8*H+32≤W)
    (hnode : ∀ node∈nodes,RationalHeight node.lo H ∧ RationalHeight node.hi H ∧ node.loValue≤5 ∧ node.hiValue≤5) :
    price model (copyRows (run model factors residual nodes).1)≤250*model.rat W := by
  apply copy_cost model _ W (by omega)
  · rw [value,List.length_map]; exact hn
  · intro c hc
    rw [value] at hc
    obtain ⟨node,hmem,rfl⟩:=List.mem_map.mp hc
    have hb:=PlayerSpecificCandidateSelection.bounds model factors residual node H hf hr hrl hH
    rw [PlayerSpecificCandidateSelection.value] at hb
    have ht:=hnode node hmem
    exact PlayerSpecificCandidateSelection.copy_cost model _ H W hb.1 hb.2.1
      (by rw [hb.2.2]; exact ht.1) (by rw [hb.2.2]; exact ht.2.1)
      (by rw [hb.2.2]; exact ht.2.2.1) (by rw [hb.2.2]; exact ht.2.2.2) (by omega) (by omega)

theorem run_cost (model : RationalCostModel) (factors residual : Data) (nodes : List Interval) (H W : ℕ)
    (hf : HasHeight factors H) (hr : HasHeight residual H) (hfl : factors.length≤3) (hrl : residual.length≤4)
    (hn : nodes.length≤3) (hH : 1≤H) (hHW : 8*H+32≤W)
    (hnode : ∀ node∈nodes,RationalHeight node.lo H ∧ RationalHeight node.hi H ∧ node.loValue≤5 ∧ node.hiValue≤5) :
    (run model factors residual nodes).2≤3000*(nodes.length+1)*model.rat W := by
  induction nodes with
  | nil =>
    have hc:=event_price model W (by omega) (.control 0) ((control_width 0).trans (by omega))
    change price model [.control 0]≤3*model.rat W at hc
    simp only [run,copyRows,List.length_nil,List.flatMap_nil,List.append_nil]
    omega
  | cons node nodes ih =>
    have ht:=hnode node List.mem_cons_self
    have hc:=PlayerSpecificCandidateSelection.run_cost model factors residual node H W hf hr hfl hrl
      ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hH hHW
    have hi:=ih (by simp only [List.length_cons] at hn; omega) (fun n hn => hnode n (List.mem_cons_of_mem node hn))
    have hcopy:=returned_copy model factors residual (node::nodes) H W hf hr hrl hn hH hHW hnode
    have hfcopy:=PlayerSpecificExtendedCopyCost.row_cost model factors H W hf (by omega) (by omega) (by omega)
    have hrcopy:=PlayerSpecificExtendedCopyCost.row_cost model residual H W hr (by omega) (by omega) (by omega)
    have hctrl:=event_price model W (by omega) (.control (node::nodes).length)
      ((control_width _).trans (by omega))
    change price model [.control (node::nodes).length]≤3*model.rat W at hctrl
    simp only [run] at hcopy ⊢
    simp only [List.length_cons] at hctrl ⊢
    nlinarith only [hc,hi,hcopy,hfcopy,hrcopy,hctrl]

end Blotto.PlayerSpecificCandidateRows
