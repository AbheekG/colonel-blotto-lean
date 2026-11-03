import Blotto.PlayerSpecificSturmNextCost

/-! Complete signed Euclidean chain preparation price, with at most four
recursive divisions and copied returned rows at each frame. -/
namespace Blotto.PlayerSpecificSturmChainCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificSturmExecution PlayerSpecificEuclideanBudget
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem chain_cost (model : RationalCostModel) (fuel : ℕ) (p q : Data) (H : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) (hcap : fuel≤4) :
    price model (chain fuel p q).2≤200000000*(fuel+1)*model.rat (width fuel H) := by
  induction fuel generalizing p q H with
  | zero =>
    have hW:=width_large 0 H
    have hh:=PlayerSpecificGCDTraceCost.header_cost model 0 p q H (width 0 H) hp hq hpl hql
      (by omega) (PlayerSpecificGCDTraceCost.input_width 0 H) (by omega)
    have hc0:=PlayerSpecificMonicDivisionBudget.control_cost model 0 (width 0 H) (by omega) (by omega)
    have hc1:=PlayerSpecificMonicDivisionBudget.control_cost model 1 (width 0 H) (by omega) (by omega)
    rw [chain]
    split
    · simp only [price_append]; nlinarith
    · have hr:=PlayerSpecificSturmCopyCost.copyRows_cost model [q] H (width 0 H)
        (by intro row hm; have he:=List.mem_singleton.mp hm; subst row; exact ⟨hq,hql⟩)
        (by change (1:ℕ)≤5; decide) (PlayerSpecificGCDTraceCost.input_width 0 H) hW
      simp only [price_append]
      nlinarith
  | succ fuel ih =>
    have hW:=width_large (fuel+1) H
    have hh:=PlayerSpecificGCDTraceCost.header_cost model (fuel+1) p q H (width (fuel+1) H) hp hq hpl hql hcap
      (PlayerSpecificGCDTraceCost.input_width (fuel+1) H) (by omega)
    have hc0:=PlayerSpecificMonicDivisionBudget.control_cost model 0 (width (fuel+1) H) (by omega) (by omega)
    have hc1:=PlayerSpecificMonicDivisionBudget.control_cost model 1 (width (fuel+1) H) (by omega) (by omega)
    rw [chain]
    split
    · simp only [price_append]
      have hm:=Nat.mul_le_mul_right (model.rat (width (fuel+1) H)) (show 1≤fuel+1+1 by omega)
      nlinarith
    · let successor := next p q
      let rest := chain fuel q successor.1
      have hn:=PlayerSpecificSturmNextCost.next_cost model (fuel+1) p q H hp hq hH hpl hql
      have hb:=PlayerSpecificSturmNextCost.bounds p q H hp hq hH hpl hql
      have hqnext:=mono hq (step_ge H)
      have hstep : 1≤step H := hH.trans (step_ge H)
      have hf : fuel≤4 := by omega
      have hi:=ih q successor.1 (step H) hqnext hb.1 hstep hql hb.2 hf
      have hip:=hi.trans (Nat.mul_le_mul_left (200000000*(fuel+1)) (model.monotone (next_width fuel H)))
      have hrH : ∀ row∈q::rest.1,HasHeight row (postHeight H) ∧ row.length≤4 := by
        intro row hm
        rcases List.mem_cons.mp hm with he | ht
        · subst row; exact ⟨mono hq (post_ge H),hql⟩
        · have hr:=chain_bounds fuel q successor.1 (step H) hqnext hb.1 hstep hql hb.2 hf row ht
          exact ⟨mono hr.1 (tail_height H),hr.2⟩
      have hrl : (q::rest.1).length≤5 := by
        have hl : rest.1.length≤fuel+1 := chain_length fuel q successor.1
        simp only [List.length_cons]
        omega
      have hcopy:=PlayerSpecificSturmCopyCost.copyRows_cost model (q::rest.1) (postHeight H) (width (fuel+1) H)
        hrH hrl (copy_width (fuel+1) H) hW
      change price model (PlayerSpecificGCDExecution.header (fuel+1) p q++successor.2++rest.2++copyRows (q::rest.1)++[.control 1])≤_
      simp only [price_append]
      nlinarith

end Blotto.PlayerSpecificSturmChainCost
