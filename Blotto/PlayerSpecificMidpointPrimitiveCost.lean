import Blotto.PlayerSpecificMidpointExecution

/-! Actual bit-buffer construction, integer casts and rational scalar
calls have source bounds at their derived operand/metadata width. -/
namespace Blotto.PlayerSpecificMidpointPrimitiveCost
open PlayerSpecificRationalTrace PlayerSpecificPolynomialHeights
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem buffer_cost (model : RationalCostModel) (K : ℕ) (bits : Fin K → Bool) (W : ℕ) (hW : K+1≤W) (h32 : 32≤W) :
    (PlayerSpecificMidpointExecution.buffer model K bits).2≤5*(K+1)*model.rat W := by
  have hw : ∀ word∈K::List.range K,binaryWordWidth word≤W := by
    intro word hw
    rcases List.mem_cons.mp hw with hw|hw
    · rw [hw]; exact (control_width K).trans hW
    · exact (control_width word).trans (by have h:=List.mem_range.mp hw; omega)
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model [] (K::List.range K) 0 W (by simp) (by simp) hw (by omega) h32
  simp only [List.length_nil,List.length_cons,List.length_range,Nat.mul_zero,Nat.zero_add] at hc
  have hR : 1≤model.rat W := (by omega : 1≤W).trans (model.word_le _)
  have hK:=Nat.mul_le_mul_left (2*K) hR
  simp only [Nat.mul_one] at hK
  change 2*K+price model (PlayerSpecificAlgebraicCallerFrame.run [] (K::List.range K))≤_
  nlinarith only [hc,hK,Nat.zero_le (model.rat W)]

theorem integer_cost (model : RationalCostModel) (n H W : ℕ) (hn : RationalHeight (n:ℚ) H)
    (hnW : binaryWordWidth n≤W) (hHW : 1+2*H≤W) (hW : 32≤W) :
    (PlayerSpecificMidpointExecution.integer model n).2≤72*model.rat W := by
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model [[(n:ℚ)]] [n,1] H W
    (by intro row hrow; simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow; rw [hrow]; exact cons_height hn (nil_height _))
    (by intro row hrow; simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow; rw [hrow]; simp)
    (by intro word hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with hw|hw
        · rw [hw]; exact hnW
        · rw [hw]; exact (control_width 1).trans (by omega)) hHW hW
  simpa only [PlayerSpecificMidpointExecution.integer,List.length_cons,List.length_nil] using hc

theorem frame_cost (model : RationalCostModel) (K index denominator : ℕ) (result : ℚ) (H W : ℕ)
    (hr : RationalHeight result H) (hK : binaryWordWidth K≤W) (hi : binaryWordWidth index≤W)
    (hd : binaryWordWidth denominator≤W) (hHW : 1+2*H≤W) (hW : 32≤W) :
    PlayerSpecificMidpointExecution.frame model K index denominator result≤78*model.rat W := by
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model [[result]] [K,index,denominator,1] H W
    (by intro row hrow; simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow; rw [hrow]; exact cons_height hr (nil_height _))
    (by intro row hrow; simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow; rw [hrow]; simp)
    (by intro word hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with hw|hw|hw|hw
        · rw [hw]; exact hK
        · rw [hw]; exact hi
        · rw [hw]; exact hd
        · rw [hw]; exact (control_width 1).trans (by omega)) hHW hW
  simpa only [PlayerSpecificMidpointExecution.frame,List.length_cons,List.length_nil] using hc

theorem scalar_cost (model : RationalCostModel) (op : Arithmetic) (a b : ℚ) (H W : ℕ)
    (ha : RationalHeight a H) (hb : RationalHeight b H) (hHW : 4*H+3≤W) :
    price model (scalar op a b).2≤15*model.rat W := by
  have hc:=price_bound model W (by omega) _ (fits_mono (scalar_fits_height op a b H ha hb) hHW)
  simpa only [scalar_length] using hc

end Blotto.PlayerSpecificMidpointPrimitiveCost
