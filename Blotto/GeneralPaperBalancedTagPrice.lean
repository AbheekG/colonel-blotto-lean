import Blotto.GeneralPaperActualOrderedDPPrice

/-! Aggregate actual balanced Rat prices by superadditivity and the proved
word totals. No per-height scaling assumption or uniform short resource
word is supplied. These sums are erased analysis, not execution passes. -/
namespace Blotto.GeneralPaperBalancedTagPrice
open GeneralPaperTagHeight
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem repeat_price (model : RationalCostModel) (n w : ℕ) : n*model.rat w≤model.rat (n*w) := by
  induction n with
  | zero => simp only [Nat.zero_mul]; exact Nat.zero_le _
  | succ n ih =>
    rw [Nat.succ_mul,Nat.succ_mul]
    exact (Nat.add_le_add_right ih _).trans (model.superadditive (n*w) w)

theorem sum_price {ι : Type*} (model : RationalCostModel) (indices : Finset ι) (width : ι → ℕ) :
    ∑ i∈indices,model.rat (width i)≤model.rat (∑ i∈indices,width i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Nat.zero_le _
  | @insert i rest hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (Nat.add_le_add_left ih _).trans (model.superadditive _ _)

theorem profile_zero (price : ℕ → ℕ) (s : ℕ) : GeneralPaperBalancedTagWords.profile price s 0=price (word s 0) := by
  simp only [GeneralPaperBalancedTagWords.profile,Nat.zero_add,Finset.sum_range_one,Nat.sub_self,pow_zero,one_mul]

theorem profile_succ (price : ℕ → ℕ) (s H : ℕ) :
    GeneralPaperBalancedTagWords.profile price s (H+1)=
      2*GeneralPaperBalancedTagWords.profile price s H+price (word s (H+1)) := by
  unfold GeneralPaperBalancedTagWords.profile
  rw [Finset.sum_range_succ]
  have hs : (∑ h∈Finset.range (H+1),2^(H+1-h)*price (word s h))=
      2*∑ h∈Finset.range (H+1),2^(H-h)*price (word s h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have he : H+1-h=(H-h)+1 := by have := Finset.mem_range.mp hh; omega
    rw [he,pow_succ]
    ring
  rw [hs]
  simp only [Nat.sub_self,pow_zero,one_mul]

theorem aggregate (model : RationalCostModel) (s H : ℕ) :
    GeneralPaperBalancedTagWords.profile model.rat s H≤model.rat ((H+1)*2^H*(2*s+2)) := by
  have hr := Finset.sum_le_sum (s:=Finset.range (H+1))
    (f:=fun h => 2^(H-h)*model.rat (word s h)) (g:=fun h => model.rat (2^(H-h)*word s h))
    (fun h _ => repeat_price model (2^(H-h)) (word s h))
  have hs := sum_price model (Finset.range (H+1)) (fun h => 2^(H-h)*word s h)
  have hw := Finset.sum_le_sum (s:=Finset.range (H+1))
    (f:=fun h => 2^(H-h)*word s h) (g:=fun h => 2^(H-h)*(word s h+1))
    (fun h _ => Nat.mul_le_mul_left _ (Nat.le_succ _))
  rw [GeneralPaperBalancedTagWords.all_level_words] at hw
  exact hr.trans (hs.trans (model.monotone hw))

end Blotto.GeneralPaperBalancedTagPrice
