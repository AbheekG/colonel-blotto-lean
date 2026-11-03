import Blotto.PlayerSpecificOriginalResourceVisitedStates

/-! Complete recursive resource-loop caller frames, including returned
state arrays, bit-block view words, frame controls and visit counters. -/
namespace Blotto.PlayerSpecificResourceLoopFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem profile (S R : ℕ) (hR : S≤R) :
    150*(2*S+1)*R+3*(5+S)*R+S≤1000*(S+1)*R := by
  nlinarith only [hR,Nat.zero_le (S*R)]

theorem cost {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (H fuel blocks visits S : ℕ)
    (hN : N≤S) (ha : s.active.length≤S) (hH : H≤S) (hf : fuel≤S) (hb : blocks≤S) (hv : visits≤S) (hS : 1≤S)
    (hm : HasHeight p.parameters.root.polynomial S) (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] S)
    (hml : p.parameters.root.polynomial.length≤4)
    (hl : ∀ j,HasHeight (p.rows.read j).length S) (hr : ∀ j,HasHeight (s.data.read j) S)
    (hll : ∀ j,(p.rows.read j).length.length≤3) (hrl : ∀ j,(s.data.read j).length≤3) :
    PlayerSpecificFiniteResourceExecution.frame model p H fuel blocks visits s≤
      1000*(S+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hW : S+1≤W := (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2
  have hframe:=PlayerSpecificAlgebraicStateFrameCost.cost model p s [] S hN ha (by simp) hm he hml hl hr hll hrl
  have hstate : price model (PlayerSpecificAlgebraicStateExecution.frame p s [])≤150*(2*S+1)*model.rat W := by
    apply hframe.trans
    apply Nat.mul_le_mul_right (model.rat W)
    apply Nat.mul_le_mul_left 150
    simp only [List.length_nil]
    omega
  have hw : ∀ word∈[H,fuel,blocks,visits,1]++List.range blocks,binaryWordWidth word≤W := by
    intro word hw
    have hsmall : word≤S := by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with (hw|hw|hw|hw|hw)|hw
      all_goals first | omega | (exact (Nat.le_of_lt (List.mem_range.mp hw)).trans hb)
    exact (control_width word).trans ((Nat.add_le_add_right hsmall 1).trans hW)
  have hcontrols:=PlayerSpecificAlgebraicCallerFrame.cost model [] ([H,fuel,blocks,visits,1]++List.range blocks) 0 W
    (by simp) (by simp) hw (by omega) (PlayerSpecificAlgebraicActiveListCost.width_large S).1
  simp only [List.length_nil,List.length_append,List.length_cons,List.length_range,Nat.mul_zero,Nat.zero_add] at hcontrols
  have hc : price model (PlayerSpecificAlgebraicCallerFrame.run [] ([H,fuel,blocks,visits,1]++List.range blocks))≤3*(5+S)*model.rat W :=
    hcontrols.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 (Nat.add_le_add_left hb 5)))
  have hsR : S≤model.rat W := (by omega : S≤W).trans (model.word_le _)
  unfold PlayerSpecificFiniteResourceExecution.frame
  exact (Nat.add_le_add (Nat.add_le_add hstate hc) hb).trans (profile S (model.rat W) hsR)

end Blotto.PlayerSpecificResourceLoopFrameCost
