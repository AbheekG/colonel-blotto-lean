import Blotto.GeneralPaperContinuousArcGeometry

/-! The geometric arc minimum is the least step value on a quantile bin
with positive-length overlap. This is the finite-range characterization
of the essential infimum used in eq:general:circle. -/
namespace Blotto.GeneralPaperContinuousArcMinimum
open MeasureTheory Set
open GeneralPaperContinuousArcGeometry GeneralPaperCircleCell
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

theorem overlap_positive_length (R W : ℕ) (hW : 0 < W) (start : ℝ)
    (L : ℕ) (hL : 0 < L) (a : Fin R) :
    Overlap R W start L a ↔ ∃ z : ℤ,
      0 < volume (Ioo start (start+L) ∩
        Ioo ((z : ℝ)*(R*W : ℕ)+(a.val : ℝ)*W)
          ((z : ℝ)*(R*W : ℕ)+((a.val : ℝ)+1)*W)) := by
  unfold Overlap
  apply exists_congr
  intro z
  rw [Ioo_inter_Ioo, Real.volume_Ioo, ENNReal.ofReal_pos]
  have hStart : start < start+L := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    linarith
  have hBin : (z : ℝ)*(R*W : ℕ)+(a.val : ℝ)*W <
      (z : ℝ)*(R*W : ℕ)+((a.val : ℝ)+1)*W := by
    have : (0 : ℝ) < W := by exact_mod_cast hW
    nlinarith
  rw [sub_pos, max_lt_iff, lt_min_iff, lt_min_iff]
  tauto

noncomputable def minimum (R W : ℕ) (start : ℝ) (L : ℕ) (x : Fin R → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ a : Fin R, Overlap R W start L a ∧ v = (R : ℝ)*x a}

theorem cell_isLeast (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (c : Fin (R*W)) (L : ℕ) (hL : 0 < L) (tau : ℝ) (ht0 : 0 < tau) (ht1 : tau < 1)
    (x : Fin R → ℝ) (hx : Monotone x) :
    IsLeast {v : ℝ | ∃ a : Fin R, Overlap R W ((c.val : ℝ)+tau) L a ∧ v = (R : ℝ)*x a}
      ((R : ℝ)*x (choice R W hR hW c L)) := by
  refine ⟨⟨choice R W hR hW c L, choice_overlaps R W hR hW c L hL tau ht0 ht1, rfl⟩, ?_⟩
  rintro v ⟨a, ha, rfl⟩
  exact mul_le_mul_of_nonneg_left (hx (choice_le_overlap R W hR hW c L tau ht0 ht1 a ha)) (Nat.cast_nonneg _)

theorem cell_minimum (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (c : Fin (R*W)) (L : ℕ) (hL : 0 < L) (tau : ℝ) (ht0 : 0 < tau) (ht1 : tau < 1)
    (x : Fin R → ℝ) (hx : Monotone x) :
    minimum R W ((c.val : ℝ)+tau) L x = (R : ℝ)*x (choice R W hR hW c L) :=
  (cell_isLeast R W hR hW c L hL tau ht0 ht1 x hx).csInf_eq

theorem minimum_mod (R W : ℕ) (s L : ℕ) (tau : ℝ) (x : Fin R → ℝ) :
    minimum R W ((s : ℝ)+tau) L x = minimum R W ((s%(R*W) : ℕ)+tau) L x := by
  unfold minimum
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, hv⟩
    exact ⟨a, (overlap_mod R W s L tau a).mp ha, hv⟩
  · rintro ⟨a, ha, hv⟩
    exact ⟨a, (overlap_mod R W s L tau a).mpr ha, hv⟩

theorem unrolled_cell_minimum (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (s L : ℕ) (hL : 0 < L) (tau : ℝ) (ht0 : 0 < tau) (ht1 : tau < 1)
    (x : Fin R → ℝ) (hx : Monotone x) :
    minimum R W ((s : ℝ)+tau) L x = (R : ℝ)*x
      (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) s 0) L) := by
  rw [minimum_mod]
  simpa only [cell, Nat.add_zero] using cell_minimum R W hR hW
    ⟨s%(R*W), Nat.mod_lt _ (Nat.mul_pos hR hW)⟩ L hL tau ht0 ht1 x hx

end Blotto.GeneralPaperContinuousArcMinimum
