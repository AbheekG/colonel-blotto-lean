import Blotto.GeneralPaperReducedInputContract

/-! Mathematical finite-cell reconstruction rule for a sorted representative
row. D=R*W cells, an arc has integer length L=R*w, and its initial point
is the midpoint c+1/2 of cell c. An arc ending across D takes the global
minimum; otherwise it takes its first touched bin. Div/mod here are erased
specification, not a declared real-RAM implementation. -/
namespace Blotto.GeneralPaperCircleCell
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable def bin (R W : ℕ) (hW : 0<W) (c : Fin (R*W)) : Fin R :=
  ⟨c.val/W,(Nat.div_lt_iff_lt_mul hW).mpr c.isLt⟩

noncomputable def choice (R W : ℕ) (hR : 0<R) (hW : 0<W) (c : Fin (R*W)) (L : ℕ) : Fin R :=
  if R*W≤c.val+L then ⟨0,hR⟩ else bin R W hW c

noncomputable def cell (D : ℕ) (hD : 0<D) (c r : ℕ) : Fin D := ⟨(c+r)%D,Nat.mod_lt _ hD⟩

theorem cell_no_wrap (D : ℕ) (hD : 0<D) (c r : ℕ) (h : c+r<D) :
    (cell D hD c r).val=c+r := Nat.mod_eq_of_lt h

theorem cell_reduce_start (D : ℕ) (hD : 0<D) (c r : ℕ) :
    cell D hD (c%D) r=cell D hD c r := by
  apply Fin.ext
  exact Nat.mod_add_mod _ _ _

theorem choice_wrapping (R W : ℕ) (hR : 0<R) (hW : 0<W) (c : Fin (R*W)) (L : ℕ)
    (h : R*W≤c.val+L) : choice R W hR hW c L=⟨0,hR⟩ := by
  rw [choice,ite_eq_left h]

theorem choice_nonwrapping (R W : ℕ) (hR : 0<R) (hW : 0<W) (c : Fin (R*W)) (L : ℕ)
    (h : c.val+L<R*W) : choice R W hR hW c L=bin R W hW c := by
  rw [choice,ite_eq_right (not_le.mpr h)]

theorem choice_le_sample_bin (R W : ℕ) (hR : 0<R) (hW : 0<W) (c : Fin (R*W)) (L r : ℕ) (hr : r<L) :
    choice R W hR hW c L≤bin R W hW (cell (R*W) (Nat.mul_pos hR hW) c.val r) := by
  by_cases h : R*W≤c.val+L
  · rw [choice_wrapping R W hR hW c L h]
    exact Nat.zero_le _
  · rw [choice_nonwrapping R W hR hW c L (Nat.lt_of_not_ge h)]
    have hc : c.val+r<R*W := by omega
    change c.val/W≤((c.val+r)%(R*W))/W
    rw [Nat.mod_eq_of_lt hc]
    exact Nat.div_le_div_right (Nat.le_add_right ..)

theorem minimum_le_sample (R W : ℕ) (hR : 0<R) (hW : 0<W) (x : Fin R → ℝ) (hx : Monotone x)
    (c : Fin (R*W)) (L r : ℕ) (hr : r<L) :
    x (choice R W hR hW c L)≤x (bin R W hW (cell (R*W) (Nat.mul_pos hR hW) c.val r)) :=
  hx (choice_le_sample_bin R W hR hW c L r hr)

theorem arc_sum (R W : ℕ) (hR : 0<R) (hW : 0<W) (x : Fin R → ℝ) (hx : Monotone x)
    (c : Fin (R*W)) (L : ℕ) :
    (L:ℝ)*x (choice R W hR hW c L)≤
      ∑ r:Fin L,x (bin R W hW (cell (R*W) (Nat.mul_pos hR hW) c.val r.val)) := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun (r : Fin L) _ => minimum_le_sample R W hR hW x hx c L r.val r.isLt)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

theorem choice_nonnegative (R W : ℕ) (hR : 0<R) (hW : 0<W) (x : Fin R → ℝ)
    (hx : ∀ a,0≤x a) (c : Fin (R*W)) (L : ℕ) : 0≤x (choice R W hR hW c L) := hx _

end Blotto.GeneralPaperCircleCell
