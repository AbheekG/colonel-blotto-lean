import Blotto.GeneralPaperProxyParameters

/-! Closed root-grid cells, including BOTH rational endpoints. The factor
four in Qg separates distinct small-denominator roots even at endpoints.
It also gives the strict Legendre criterion for every point in the cell.
-/
namespace Blotto.GeneralPaperProxyCell
open GeneralPaperBucketGeometry
set_option autoImplicit false
set_option maxHeartbeats 2500000

def Closed (Q j : ℕ) (x : ℚ) : Prop := lower Q j≤x ∧ x≤upper Q j

theorem distance_closed (Q j : ℕ) (hQ : 0<Q) (x : ℚ) (hx : Closed Q j x) :
    |GeneralPaperBucketGeometry.midpoint Q j-x|≤1/(2*(Q:ℚ)) := by
  rw [abs_le]
  have hl := midpoint_left Q j hQ
  have hr := midpoint_right Q j hQ
  exact ⟨by linarith only [hx.2,hr],by linarith only [hx.1,hl]⟩

theorem closed_of_distance (Q j : ℕ) (hQ : 0<Q) (x : ℚ)
    (h : |GeneralPaperBucketGeometry.midpoint Q j-x|≤1/(2*(Q:ℚ))) : Closed Q j x := by
  have ha := abs_le.mp h
  have hl := midpoint_left Q j hQ
  have hr := midpoint_right Q j hQ
  exact ⟨by linarith only [ha.2,hl],by linarith only [ha.1,hr]⟩

theorem closed_equal (H Q j : ℕ) (hH : 0<H) (hScale : 4*H*H≤Q)
    (x y : Farey.Fraction) (hx : x.den≤H) (hy : y.den≤H)
    (hX : Closed Q j x.value) (hY : Closed Q j y.value) : x.value=y.value := by
  have hQ : 0<Q := by nlinarith
  have hw := width Q j hQ
  have hs : (H:ℚ)*H<(Q:ℚ) := by exact_mod_cast (show H*H<Q by nlinarith)
  have hi : 1/(Q:ℚ)<1/((H:ℚ)*H) := one_div_lt_one_div_of_lt (by positivity) hs
  rcases lt_trichotomy x.value y.value with h|h|h
  · have hg := Farey.bounded_separation H hx hy h
    linarith only [hg,hi,hX.1,hY.2,hw]
  · exact h
  · have hg := Farey.bounded_separation H hy hx h
    linarith only [hg,hi,hY.1,hX.2,hw]

theorem regular_convergent (H Q j : ℕ) (hH : 0<H) (hScale : 4*H*H≤Q)
    (x : Farey.Fraction) (hx : x.den≤H) (hX : Closed Q j x.value) :
    ∃ n, x.value=Real.convergent (GeneralPaperBucketGeometry.midpoint Q j:ℝ) n := by
  have hQ : 0<Q := by nlinarith
  have hd := (Farey.value_den_le x).trans hx
  have hs : x.value.den*x.value.den<Q := by nlinarith
  have hs' : 2*(x.value.den:ℚ)^2<2*(Q:ℚ) := by
    have hc : (x.value.den:ℚ)*(x.value.den:ℚ)<(Q:ℚ) := by exact_mod_cast hs
    nlinarith only [hc]
  have hi : 1/(2*(Q:ℚ))<1/(2*(x.value.den:ℚ)^2) :=
    one_div_lt_one_div_of_lt (by positivity) hs'
  have hRat := (distance_closed Q j hQ x.value hX).trans_lt hi
  have hReal : |(GeneralPaperBucketGeometry.midpoint Q j:ℝ)-(x.value:ℝ)|<1/(2*(x.value.den:ℝ)^2) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr hRat
    simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_mul,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using hh
  exact Real.exists_rat_eq_convergent hReal

end Blotto.GeneralPaperProxyCell
