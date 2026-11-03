import Blotto.GeneralPaperNativeMixedCircleSecurity

/-! Positive overlap of a rotating arc with the periodic quantile bins.
Coordinates here are in cell units: period D=R*W, each bin has width W.
An arc beginning at c+tau, 0<tau<1, has the checked cell minimum. -/
namespace Blotto.GeneralPaperContinuousArcGeometry
open MeasureTheory Set
open GeneralPaperCircleCell
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def Overlap (R W : ℕ) (start : ℝ) (L : ℕ) (a : Fin R) : Prop :=
  ∃ z : ℤ, start < (z : ℝ)*(R*W : ℕ) + ((a.val : ℝ)+1)*W ∧
    (z : ℝ)*(R*W : ℕ) + (a.val : ℝ)*W < start + L

theorem overlap_period (R W : ℕ) (start : ℝ) (L : ℕ) (a : Fin R) (q : ℤ) :
    Overlap R W (start + (q : ℝ)*(R*W : ℕ)) L a ↔ Overlap R W start L a := by
  constructor
  · rintro ⟨z, h1, h2⟩
    refine ⟨z-q, ?_, ?_⟩ <;> push_cast at * <;> ring_nf at * <;> linarith
  · rintro ⟨z, h1, h2⟩
    refine ⟨z+q, ?_, ?_⟩ <;> push_cast at * <;> ring_nf at * <;> linarith

theorem overlap_mod (R W : ℕ) (s L : ℕ) (tau : ℝ) (a : Fin R) :
    Overlap R W ((s : ℝ)+tau) L a ↔ Overlap R W ((s%(R*W) : ℕ)+tau) L a := by
  have he : (s : ℝ) = (s%(R*W) : ℕ) + ((s/(R*W) : ℕ) : ℝ)*(R*W : ℕ) := by
    exact_mod_cast (calc s = s%(R*W)+(R*W)*(s/(R*W)) := (Nat.mod_add_div s (R*W)).symm
                        _ = s%(R*W)+(s/(R*W))*(R*W) := by ring)
  have hh : (s : ℝ)+tau = ((s%(R*W) : ℕ) : ℝ)+tau+
      (((s/(R*W) : ℕ) : ℤ) : ℝ)*(R*W : ℕ) := by
    simp only [Int.cast_natCast]
    rw [he]
    ring
  rw [hh]
  exact overlap_period R W ((s%(R*W) : ℕ)+tau) L a ((s/(R*W) : ℕ) : ℤ)

theorem overlap_zero_period {R W L : ℕ} (hR : 0 < R) (hW : 0 < W)
    (c : Fin (R*W)) (tau : ℝ) (ht0 : 0 < tau) (ht1 : tau < 1)
    (hNo : c.val+L < R*W) (a : Fin R)
    (hz : Overlap R W ((c.val : ℝ)+tau) L a) :
    (c.val : ℝ)+tau < ((a.val : ℝ)+1)*W ∧ (a.val : ℝ)*W < (c.val : ℝ)+tau+L := by
  obtain ⟨z, h1, h2⟩ := hz
  have hD : (0 : ℝ) < (R*W : ℕ) := by exact_mod_cast Nat.mul_pos hR hW
  have hA : ((a.val : ℝ)+1)*W ≤ (R*W : ℕ) := by
    have hn : (a.val+1)*W ≤ R*W := Nat.mul_le_mul_right W (by omega)
    exact_mod_cast hn
  have hA0 : (0 : ℝ) ≤ (a.val : ℝ)*W := by positivity
  have hEnd : (c.val : ℝ)+tau+L < (R*W : ℕ) := by
    have hn : (c.val : ℝ)+L+1 ≤ (R*W : ℕ) := by exact_mod_cast (show c.val+L+1 ≤ R*W by omega)
    linarith
  have hz0 : z = 0 := by
    by_contra h
    have hc0 : (0 : ℝ) ≤ c.val := Nat.cast_nonneg _
    rcases (show z ≤ -1 ∨ 1 ≤ z by omega) with hzNeg | hzPos
    · have hzR : (z : ℝ) ≤ -1 := by exact_mod_cast hzNeg
      have hm := mul_le_mul_of_nonneg_right hzR hD.le
      linarith
    · have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hzPos
      have hm := mul_le_mul_of_nonneg_right hzR hD.le
      linarith
  subst z
  simpa only [Int.cast_zero, zero_mul, zero_add] using And.intro h1 h2

theorem choice_overlaps (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (c : Fin (R*W)) (L : ℕ) (hL : 0 < L) (tau : ℝ) (ht0 : 0 < tau) (ht1 : tau < 1) :
    Overlap R W ((c.val : ℝ)+tau) L (choice R W hR hW c L) := by
  by_cases hWrap : R*W ≤ c.val+L
  · rw [choice_wrapping R W hR hW c L hWrap]
    refine ⟨1, ?_, ?_⟩
    · have hc : (c.val : ℝ)+1 ≤ (R*W : ℕ) := by exact_mod_cast (show c.val+1 ≤ R*W by omega)
      have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
      norm_num only [Int.cast_one, one_mul, Fin.val_zero, Nat.cast_zero, zero_add]
      linarith
    · have hc : (R*W : ℕ) ≤ (c.val : ℝ)+L := by exact_mod_cast hWrap
      norm_num only [Int.cast_one, one_mul, Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
      linarith
  · rw [choice_nonwrapping R W hR hW c L (by omega)]
    refine ⟨0, ?_, ?_⟩
    · have hn : c.val+1 ≤ (c.val/W+1)*W := by
        have hmod := Nat.mod_lt c.val hW
        have he := Nat.mod_add_div c.val W
        nlinarith only [hmod, he]
      have hr : (c.val : ℝ)+1 ≤ ((c.val/W : ℕ)+1 : ℝ)*W := by exact_mod_cast hn
      simp only [bin, Int.cast_zero, zero_mul, zero_add]
      linarith
    · have hn := Nat.div_mul_le_self c.val W
      have hr : ((c.val/W : ℕ) : ℝ)*W ≤ c.val := by exact_mod_cast hn
      simp only [bin, Int.cast_zero, zero_mul, zero_add]
      have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
      linarith

theorem choice_le_overlap (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (c : Fin (R*W)) (L : ℕ) (tau : ℝ) (ht0 : 0 < tau) (ht1 : tau < 1)
    (a : Fin R) (ha : Overlap R W ((c.val : ℝ)+tau) L a) :
    choice R W hR hW c L ≤ a := by
  by_cases hWrap : R*W ≤ c.val+L
  · rw [choice_wrapping R W hR hW c L hWrap]
    exact Nat.zero_le _
  · rw [choice_nonwrapping R W hR hW c L (by omega)]
    have hh := (overlap_zero_period hR hW c tau ht0 ht1 (by omega) a ha).1
    change c.val/W ≤ a.val
    by_contra h
    have hn : (a.val+1)*W ≤ c.val :=
      (Nat.mul_le_mul_right W (show a.val+1 ≤ c.val/W by omega)).trans (Nat.div_mul_le_self _ _)
    have hr : ((a.val : ℝ)+1)*W ≤ c.val := by exact_mod_cast hn
    linarith

end Blotto.GeneralPaperContinuousArcGeometry
