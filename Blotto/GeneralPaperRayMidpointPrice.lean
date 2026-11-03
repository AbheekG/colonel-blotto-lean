import Blotto.GeneralPaperBudgetCrossingPrice

/-! Price the actual rational bracket midpoint, including its literal,
addition, division and result writes. This is not the integer rank midpoint.
-/
namespace Blotto.GeneralPaperRayMidpointPrice
open GeneralPaperRationalPrimitivePrice
set_option autoImplicit false

def run (primitive : ℕ → ℕ) (W : ℕ) (lo hi : ℚ) : ℚ × ℕ :=
  let sum := lo+hi
  (sum/2,16*W+primitive (rationalWordWidth (2:ℚ))+binary primitive (·+·) lo hi+
    binary primitive (·/·) sum 2)

theorem data (primitive : ℕ → ℕ) (W : ℕ) (lo hi : ℚ) : (run primitive W lo hi).1=(lo+hi)/2 := rfl

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W R : ℕ) (lo hi : ℚ)
    (hl : RationalHeight lo R) (hh : RationalHeight hi R) :
    (run primitive W lo hi).2≤16*W+5*primitive (4*R+7) := by
  have hs := hl.add hh
  have hm := GeneralPaperRayAffineBound.midpoint_height hl hh
  have hTwo : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hL := hl.mono (show R≤2*R+3 by omega)
  have hH := hh.mono (show R≤2*R+3 by omega)
  have hS := hs.mono (show R+R+1≤2*R+3 by omega)
  have h2 := hTwo.mono (show 2≤2*R+3 by omega)
  have hc := hMono (rationalWordWidth_of_height h2)
  have ha := binary_le primitive hMono (·+·) lo hi _
    (rationalWordWidth_of_height hL) (rationalWordWidth_of_height hH) (rationalWordWidth_of_height hS)
  have hd := binary_le primitive hMono (·/·) (lo+hi) 2 _
    (rationalWordWidth_of_height hS) (rationalWordWidth_of_height h2) (rationalWordWidth_of_height hm)
  have he : 1+2*(2*R+3)=4*R+7 := by ring
  rw [he] at hc ha hd
  change 16*W+primitive (rationalWordWidth (2:ℚ))+binary primitive (·+·) lo hi+binary primitive (·/·) (lo+hi) 2≤_
  omega

end Blotto.GeneralPaperRayMidpointPrice
