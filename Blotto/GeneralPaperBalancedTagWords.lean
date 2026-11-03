import Blotto.GeneralPaperOrderedDPHeight

/-! Exact balanced-level amortization of resource words. At height h a
tag can use 2^h times the leaf word, but only 2^(H-h) nodes have that height.
Primitive Rat prices remain explicit until the fast-bit profile is joined. -/
namespace Blotto.GeneralPaperBalancedTagWords
open GeneralPaperTagHeight
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem word_succ (s h : ℕ) : word s (h+1)=2*word s h+1 := by
  rw [word,expressionHeightBudget_succ,word]
  ring

theorem word_affine (s h : ℕ) : word s h+1=2^h*(2*s+2) := by
  induction h with
  | zero => rw [word_zero,pow_zero]; omega
  | succ h ih => rw [word_succ,pow_succ]; nlinarith only [ih]

theorem level_words (s H h : ℕ) (hh : h≤H) :
    2^(H-h)*(word s h+1)=2^H*(2*s+2) := by
  rw [word_affine,←Nat.mul_assoc,←pow_add,Nat.sub_add_cancel hh]

theorem all_level_words (s H : ℕ) :
    ∑ h∈Finset.range (H+1),2^(H-h)*(word s h+1)=(H+1)*2^H*(2*s+2) := by
  have he : (∑ h∈Finset.range (H+1),2^(H-h)*(word s h+1))=
      ∑ _h∈Finset.range (H+1),2^H*(2*s+2) := by
    apply Finset.sum_congr rfl
    intro h hh
    exact level_words s H h (by have := Finset.mem_range.mp hh; omega)
  rw [he]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]
  ring

def profile (price : ℕ → ℕ) (s H : ℕ) : ℕ :=
  ∑ h∈Finset.range (H+1),2^(H-h)*price (word s h)

theorem uniform_profile (price : ℕ → ℕ) (hMono : Monotone price) (s H : ℕ) :
    profile price s H≤(H+1)*2^H*price (word s H) := by
  unfold profile
  have h := Finset.sum_le_sum (s:=Finset.range (H+1)) (f:=fun h => 2^(H-h)*price (word s h))
    (g:=fun _ => 2^H*price (word s H)) (by
      intro h hh
      have hv := Finset.mem_range.mp hh
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.sub_le _ _))
        (hMono (word_mono s h H (by omega))))
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,Nat.mul_assoc] using h

end Blotto.GeneralPaperBalancedTagWords
