import Blotto.PlayerSpecificSegmentSelectionExecution

/-! Complete saved mass/probability/next rows, weight table, finite
indices, block views and returned choice/visit-counter source frames. -/
namespace Blotto.PlayerSpecificSegmentSelectionFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost {slots : ℕ} (model : RationalCostModel) (root : Candidate) (weights : FixedArrayTable slots Data)
    (fallback : Fin slots) (H : ℕ) (items : List (Fin slots)) (remaining probability next : Data) (blocks : ℕ) (result : Fin slots×ℕ)
    (U : ℕ) (hm : HasHeight root.polynomial U) (hml : root.polynomial.length≤4)
    (he : HasHeight [root.interval.lo,root.interval.hi] U)
    (hr : HasHeight remaining U) (hrl : remaining.length≤3) (hp : HasHeight probability U) (hpl : probability.length≤3)
    (hn : HasHeight next U) (hnl : next.length≤3) (hw : ∀ j,HasHeight (weights.read j) U ∧ (weights.read j).length≤3)
    (hitems : items.length≤slots) (hslots : slots≤U) (hH : H≤U) (hblocks : blocks≤U) (hvisits : result.2≤U) (hU : 1≤U) :
    price model (PlayerSpecificSegmentSelectionExecution.frame root weights fallback H items remaining probability next blocks result)≤
      1000*(slots+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width U) := by
  let rows:=[root.polynomial,[root.interval.lo,root.interval.hi],remaining,probability,next]++List.ofFn weights.read
  let words:=[slots,H,fallback.val,items.length,blocks,result.1.val,result.2,1]++items.map Fin.val
  let W:=PlayerSpecificAlgebraicComparisonExecution.width U
  have hrows : ∀ row∈rows,HasHeight row U ∧ row.length≤21 := by
    intro row hrow
    simp only [rows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with (hrow|hrow|hrow|hrow|hrow)|hrow
    · rw [hrow]; exact ⟨hm,by omega⟩
    · rw [hrow]; exact ⟨he,by simp⟩
    · rw [hrow]; exact ⟨hr,by omega⟩
    · rw [hrow]; exact ⟨hp,by omega⟩
    · rw [hrow]; exact ⟨hn,by omega⟩
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow
      exact ⟨(hw j).1,(hw j).2.trans (by decide)⟩
  have hwords : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hword
    have hsmall : word≤U := by
      simp only [words,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hword
      rcases hword with (hword|hword|hword|hword|hword|hword|hword|hword)|hword
      · omega
      · omega
      · have h:=fallback.isLt; omega
      · omega
      · omega
      · have h:=result.1.isLt; omega
      · omega
      · omega
      · obtain ⟨j,_,rfl⟩:=List.mem_map.mp hword; have h:=j.isLt; omega
    exact (control_width word).trans ((Nat.add_le_add_right hsmall 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large U).2.2)
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model rows words U W
    (fun row hrow => (hrows row hrow).1) (fun row hrow => (hrows row hrow).2) hwords
    (PlayerSpecificAlgebraicActiveListCost.width_large U).2.1 (PlayerSpecificAlgebraicActiveListCost.width_large U).1
  apply hc.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [rows,words,List.length_append,List.length_cons,List.length_nil,List.length_ofFn,List.length_map]
  omega

end Blotto.PlayerSpecificSegmentSelectionFrameCost
