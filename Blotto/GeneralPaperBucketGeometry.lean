import Blotto.GeneralPaperNativeRowBudget
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-! Exact bucket geometry for the selected union of grid and Farey bids.
There is at most one bounded-denominator value in a strict bucket interior.
Any such value satisfies the regular-convergent criterion at the midpoint.
These are correctness facts for the selected continued-fraction query, not
an enumeration or an alternative predecessor algorithm.
-/
namespace Blotto.GeneralPaperBucketGeometry
set_option autoImplicit false
set_option maxHeartbeats 2500000

def lower (C t : ℕ) : ℚ := (t:ℚ)/C

def upper (C t : ℕ) : ℚ := ((t:ℚ)+1)/C

def midpoint (C t : ℕ) : ℚ := (2*(t:ℚ)+1)/(2*(C:ℚ))

def Interior (C t : ℕ) (x : ℚ) : Prop := lower C t<x ∧ x<upper C t

theorem width (C t : ℕ) (hC : 0<C) : upper C t-lower C t=1/(C:ℚ) := by
  unfold upper lower
  ring

theorem midpoint_left (C t : ℕ) (hC : 0<C) : midpoint C t-lower C t=1/(2*(C:ℚ)) := by
  have hc : (C:ℚ)≠0 := by exact_mod_cast hC.ne'
  unfold midpoint lower
  field_simp
  ring

theorem midpoint_right (C t : ℕ) (hC : 0<C) : upper C t-midpoint C t=1/(2*(C:ℚ)) := by
  have hc : (C:ℚ)≠0 := by exact_mod_cast hC.ne'
  unfold midpoint upper
  field_simp
  ring

theorem midpoint_distance (C t : ℕ) (hC : 0<C) (x : ℚ) (hx : Interior C t x) :
    |midpoint C t-x|<1/(2*(C:ℚ)) := by
  rw [abs_lt]
  have hl := midpoint_left C t hC
  have hr := midpoint_right C t hC
  exact ⟨by linarith only [hx.2,hr],by linarith only [hx.1,hl]⟩

theorem interiors_equal (D C t : ℕ) (hD : 0<D) (hScale : D*D≤C)
    (x y : Farey.Fraction) (hx : x.den≤D) (hy : y.den≤D)
    (hX : Interior C t x.value) (hY : Interior C t y.value) : x.value=y.value := by
  have hC : 0<C := (Nat.mul_pos hD hD).trans_le hScale
  have hWidth := width C t hC
  have hLower : 1/(C:ℚ)≤1/((D:ℚ)*D) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hScale)
  rcases lt_trichotomy x.value y.value with h|h|h
  · have hs := Farey.bounded_separation D hx hy h
    linarith only [hs,hLower,hX.1,hY.2,hWidth]
  · exact h
  · have hs := Farey.bounded_separation D hy hx h
    linarith only [hs,hLower,hY.1,hX.2,hWidth]

theorem midpoint_criterion (D C t : ℕ) (hD : 0<D) (hScale : D*D≤C)
    (x : Farey.Fraction) (hx : x.den≤D) (hX : Interior C t x.value) :
    |midpoint C t-x.value|<1/(2*(x.value.den:ℚ)^2) := by
  have hC : 0<C := (Nat.mul_pos hD hD).trans_le hScale
  have hd := (Farey.value_den_le x).trans hx
  have hm : x.value.den*x.value.den≤C := (Nat.mul_le_mul hd hd).trans hScale
  have hp : (0:ℚ)<2*(x.value.den:ℚ)^2 := by positivity
  have he : 2*(x.value.den:ℚ)^2≤2*(C:ℚ) := by
    have hc : (x.value.den:ℚ)*(x.value.den:ℚ)≤(C:ℚ) := by exact_mod_cast hm
    nlinarith only [hc]
  exact (midpoint_distance C t hC x.value hX).trans_le (one_div_le_one_div_of_le hp he)

theorem interior_regular_convergent (D C t : ℕ) (hD : 0<D) (hScale : D*D≤C)
    (x : Farey.Fraction) (hx : x.den≤D) (hX : Interior C t x.value) :
    ∃ n, x.value=Real.convergent (midpoint C t:ℝ) n := by
  have hRat := midpoint_criterion D C t hD hScale x hx hX
  have hReal : |(midpoint C t:ℝ)-(x.value:ℝ)|<1/(2*(x.value.den:ℝ)^2) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hRat
    simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_mul,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using hh
  exact Real.exists_rat_eq_convergent hReal

end Blotto.GeneralPaperBucketGeometry
