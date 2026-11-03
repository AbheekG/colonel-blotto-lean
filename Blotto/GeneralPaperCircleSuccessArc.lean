import Blotto.GeneralPaperSelectedArcDiscrepancy

/-! Successful circle-minimum threshold cells form a single integer
circular interval, including zero/full ranks. This identifies the actual
reconstruction rule with the selected-shift discrepancy theorem. -/
namespace Blotto.GeneralPaperCircleSuccessArc
open GeneralPaperCircleCell GeneralPaperSelectedCircularArc
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem success_iff (R W : ℕ) (hR : 0<R) (hW : 0<W) (L f : ℕ) (hf : 0<f) (c : Fin (R*W)) :
    (choice R W hR hW c L).val<f ↔ c.val<f*W ∨ R*W≤c.val+L := by
  by_cases hw:R*W≤c.val+L
  · rw [choice_wrapping R W hR hW c L hw]
    change 0<f ↔ _
    exact iff_of_true hf (Or.inr hw)
  · rw [choice_nonwrapping R W hR hW c L (Nat.lt_of_not_ge hw)]
    change c.val/W<f ↔ _
    rw [Nat.div_lt_iff_lt_mul hW]
    simp only [hw,or_false]

theorem event_arc (R W : ℕ) (hR : 0<R) (hW : 0<W) (L f : ℕ) (hL : L≤R*W) (hf : f≤R) :
    ∃ (start:Fin (R*W)) (length:ℕ),length≤R*W ∧
      ∀ c:Fin (R*W),(choice R W hR hW c L).val<f ↔ arc start length c := by
  have hD := Nat.mul_pos hR hW
  by_cases hf0:f=0
  · subst f
    refine ⟨⟨0,hD⟩,0,Nat.zero_le _,?_⟩
    intro c
    simp only [arc,Nat.not_lt_zero]
  have hfPos : 0<f := Nat.pos_of_ne_zero hf0
  have hfW := Nat.mul_le_mul_right W hf
  by_cases hL0:L=0
  · subst L
    refine ⟨⟨0,hD⟩,f*W,hfW,?_⟩
    intro c
    rw [success_iff R W hR hW 0 f hfPos c,arc_interval]
    have hc : ¬R*W≤c.val+0 := by have h := c.isLt;omega
    simp only [hc,or_false,Nat.zero_add,ite_eq_left hfW,Nat.zero_le,true_and]
  have hLPos : 0<L := Nat.pos_of_ne_zero hL0
  let start : Fin (R*W) := ⟨R*W-L,by omega⟩
  by_cases hFull:R*W≤L+f*W
  · refine ⟨start,R*W,le_rfl,?_⟩
    intro c
    have hSuccess : (choice R W hR hW c L).val<f := by
      rw [success_iff R W hR hW L f hfPos c]
      omega
    exact iff_of_true hSuccess (c-start).isLt
  · refine ⟨start,L+f*W,(Nat.le_of_lt (Nat.lt_of_not_ge hFull)),?_⟩
    intro c
    rw [success_iff R W hR hW L f hfPos c,arc_interval]
    have hPos := Nat.mul_pos hfPos hW
    have hWrap : ¬start.val+(L+f*W)≤R*W := by dsimp only [start];omega
    rw [ite_eq_right hWrap]
    dsimp only [start]
    omega

end Blotto.GeneralPaperCircleSuccessArc
