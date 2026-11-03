import Blotto.GeneralPaperSelectedPrefixCount

/-! Integer circular intervals and their exact rotation. Both wrapped and
ordinary intervals use differences of the same two prefixIndicator indicators. -/
namespace Blotto.GeneralPaperSelectedCircularArc
open GeneralPaperCircleCell
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 900000

def arc {D : ℕ} (start : Fin D) (L : ℕ) (c : Fin D) : Prop := (c-start).val<L

theorem arc_interval {D : ℕ} (start : Fin D) (L : ℕ) (c : Fin D) :
    arc start L c ↔ if start.val+L≤D then start.val≤c.val ∧ c.val<start.val+L
      else start.val≤c.val ∨ c.val<start.val+L-D := by
  unfold arc
  have hc := c.isLt
  have hs := start.isLt
  by_cases h:start≤c
  · rw [Fin.sub_val_of_le h]
    have hh : start.val≤c.val := h
    split_ifs <;> omega
  · have hh : c.val<start.val := Nat.lt_of_not_ge h
    rw [Fin.val_sub,Nat.mod_eq_of_lt (by omega : D-start.val+c.val<D)]
    split_ifs <;> omega

noncomputable def prefixIndicator {D : ℕ} (A : ℕ) (c : Fin D) : ℝ := if c.val<A then 1 else 0

theorem ordinary_indicator (a b x : ℕ) (hab : a≤b) :
    (if a≤x ∧ x<b then (1:ℝ) else 0)=(if x<b then 1 else 0)-(if x<a then 1 else 0) := by
  by_cases ha:x<a
  · have hb : x<b := ha.trans_le hab
    simp [ha,hb,not_le_of_gt ha]
  · have ha' : a≤x := Nat.le_of_not_gt ha
    by_cases hb:x<b <;> simp [ha,ha',hb]

theorem wrapped_indicator (a b x : ℕ) (hba : b≤a) :
    (if a≤x ∨ x<b then (1:ℝ) else 0)=1+(if x<b then 1 else 0)-(if x<a then 1 else 0) := by
  by_cases ha:x<a
  · by_cases hb:x<b <;> simp [ha,hb,not_le_of_gt ha]
  · have ha' : a≤x := Nat.le_of_not_gt ha
    have hb : ¬x<b := not_lt_of_ge (hba.trans ha')
    simp [ha,ha',hb]

theorem arc_indicator {D : ℕ} (start : Fin D) (L : ℕ) (hL : L≤D) (c : Fin D) :
    (if arc start L c then (1:ℝ) else 0)=
      if start.val+L≤D then prefixIndicator (start.val+L) c-prefixIndicator start.val c
      else 1+prefixIndicator (start.val+L-D) c-prefixIndicator start.val c := by
  by_cases h:start.val+L≤D
  · rw [ite_eq_left h,arc_interval start L c,ite_eq_left h]
    have hi := ordinary_indicator start.val (start.val+L) c.val (Nat.le_add_right ..)
    by_cases hc:start.val≤c.val ∧ c.val<start.val+L
    · simpa only [prefixIndicator,ite_eq_left hc] using hi
    · simpa only [prefixIndicator,ite_eq_right hc] using hi
  · rw [ite_eq_right h,arc_interval start L c,ite_eq_right h]
    have hi := wrapped_indicator start.val (start.val+L-D) c.val (by omega : start.val+L-D≤start.val)
    by_cases hc:start.val≤c.val ∨ c.val<start.val+L-D
    · simpa only [prefixIndicator,ite_eq_left hc] using hi
    · simpa only [prefixIndicator,ite_eq_right hc] using hi

theorem rotated (D : ℕ) (hD : 0<D) (start : Fin D) (L shift : ℕ) (c : Fin D) :
    arc start L (cell D hD shift c.val) ↔ arc (start-⟨shift%D,Nat.mod_lt _ hD⟩) L c := by
  let : NeZero D := ⟨hD.ne'⟩
  let p : Fin D := ⟨shift%D,Nat.mod_lt _ hD⟩
  have he : cell D hD shift c.val=c+p := by
    apply Fin.ext
    change (shift+c.val)%D=(c.val+shift%D)%D
    rw [Nat.add_mod_mod,Nat.add_comm shift c.val]
  unfold arc
  rw [he]
  have ha : c+p-start=c-(start-p) := by abel
  rw [ha]

end Blotto.GeneralPaperSelectedCircularArc
