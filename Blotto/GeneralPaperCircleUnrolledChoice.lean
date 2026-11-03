import Blotto.GeneralPaperCircleOddGeometry

/-! The paper's unrolled odd-coordinate branch computes exactly the
finite-cell circle minimum index. A second-lap endpoint uses bin a-R;
only an arc crossing the first circle boundary takes the global minimum. -/
namespace Blotto.GeneralPaperCircleUnrolledChoice
open GeneralPaperCircleCell
set_option autoImplicit false
set_option maxHeartbeats 1600000

def select (R D left right a : ℕ) : ℕ :=
  if left<2*D ∧ 2*D<right then 0 else if a<R then a else a-R

theorem second_lap_division (R W u : ℕ) (hW : 0<W) (hu : R*W≤u) : u/W-R=(u-R*W)/W := by
  have he : u=(u-R*W)+W*R := by nlinarith only [Nat.sub_add_cancel hu]
  have hd := Nat.add_mul_div_left (u-R*W) R hW
  rw [←he] at hd
  rw [hd,Nat.add_sub_cancel]

theorem data (R W : ℕ) (hR : 0<R) (hW : 0<W) (t offset length : ℕ)
    (ht : t<R*W) (hLength : offset+length≤R*W) :
    select R (R*W) (2*(t+offset)+1) (2*(t+offset+length)+1) ((t+offset)/W)=
      (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) t offset) length).val := by
  let u := t+offset
  have hu : u<2*(R*W) := by dsimp only [u];omega
  by_cases hFirst:u<R*W
  · have hc : (cell (R*W) (Nat.mul_pos hR hW) t offset).val=u := cell_no_wrap _ _ t offset hFirst
    have ha : u/W<R := (Nat.div_lt_iff_lt_mul hW).mpr hFirst
    by_cases hCross:2*u+1<2*(R*W) ∧ 2*(u+length)+1>2*(R*W)
    · have hw : R*W≤(cell (R*W) (Nat.mul_pos hR hW) t offset).val+length := by rw [hc];omega
      change select R (R*W) (2*u+1) (2*(u+length)+1) (u/W)=_
      rw [select,ite_eq_left hCross,choice_wrapping R W hR hW _ length hw]
    · have hn : (cell (R*W) (Nat.mul_pos hR hW) t offset).val+length<R*W := by rw [hc];omega
      change select R (R*W) (2*u+1) (2*(u+length)+1) (u/W)=_
      rw [select,ite_eq_right hCross,ite_eq_left ha,choice_nonwrapping R W hR hW _ length hn]
      change u/W=(cell (R*W) (Nat.mul_pos hR hW) t offset).val/W
      rw [hc]
  · have hU : R*W≤u := Nat.le_of_not_gt hFirst
    have hSub : u-R*W+R*W=u := Nat.sub_add_cancel hU
    have hc : (cell (R*W) (Nat.mul_pos hR hW) t offset).val=u-R*W := by
      change u%(R*W)=u-R*W
      exact Nat.mod_eq_sub_mod hU |>.trans (Nat.mod_eq_of_lt (by omega))
    have ha : R≤u/W := (Nat.le_div_iff_mul_le hW).mpr hU
    have hn : (cell (R*W) (Nat.mul_pos hR hW) t offset).val+length<R*W := by rw [hc];dsimp only [u] at hSub;omega
    have hCross : ¬(2*u+1<2*(R*W) ∧ 2*(u+length)+1>2*(R*W)) := by omega
    change select R (R*W) (2*u+1) (2*(u+length)+1) (u/W)=_
    rw [select,ite_eq_right hCross,ite_eq_right (Nat.not_lt_of_ge ha),choice_nonwrapping R W hR hW _ length hn]
    change u/W-R=(cell (R*W) (Nat.mul_pos hR hW) t offset).val/W
    rw [hc,second_lap_division R W u hW hU]

theorem cursor_data (R W : ℕ) (hR : 0<R) (hW : 0<W) (t offset length a next : ℕ)
    (ht : t<R*W) (hLength : offset+length≤R*W)
    (hNext : next=(a+1)*(2*W)) (hLower : a*(2*W)<2*(t+offset)+1) :
    select R (R*W) (2*(t+offset)+1) (2*(t+offset+length)+1)
      (GeneralPaperCircleBinAdvance.run (2*W) (2*(t+offset)+1) (2*R) a next).bin=
        (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) t offset) length).val := by
  have hu : t+offset<2*(R*W) := by omega
  rw [(GeneralPaperCircleOddGeometry.cursor_bin R W (t+offset) a next hR hW hu hNext hLower).1]
  exact data R W hR hW t offset length ht hLength

end Blotto.GeneralPaperCircleUnrolledChoice
