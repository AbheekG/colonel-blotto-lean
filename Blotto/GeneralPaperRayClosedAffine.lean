import Blotto.GeneralPaperRayActualParametricDP

/-! Elementary closed-endpoint consequences for rational affine functions.
These are erased order arguments, with no numerical limit or approximation
in the executed crossing procedure.
-/
namespace Blotto.GeneralPaperRayClosedAffine
open GeneralPaperRayAffine GeneralPaperRayAffineComparison
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem nonpositive_closed (a : Affine) (lo hi : ℚ) (hOrder : lo<hi)
    (hOpen : ∀ t,lo<t ∧ t<hi → a.value t≤0) : a.value lo≤0 ∧ a.value hi≤0 := by
  rcases lt_trichotomy a.slope 0 with hn|hz|hp
  · have hc : a.crossing≤lo := by
      by_contra hBad
      have hRoot : lo<a.crossing := lt_of_not_ge hBad
      obtain ⟨t,htL,htH⟩ := exists_between (lt_min hOrder hRoot)
      have hValue := (negative_iff a hn t).mp (hOpen t ⟨htL,htH.trans_le (min_le_left _ _)⟩)
      exact (not_lt_of_ge hValue) (htH.trans_le (min_le_right _ _))
    exact ⟨(negative_iff a hn lo).mpr hc,(negative_iff a hn hi).mpr (hc.trans hOrder.le)⟩
  · have hh := hOpen ((lo+hi)/2) (GeneralPaperRayStableMinimum.midpoint_inside lo hi hOrder)
    simpa only [Affine.value,hz,zero_mul,add_zero,and_self] using hh
  · have hc : hi≤a.crossing := by
      by_contra hBad
      have hRoot : a.crossing<hi := lt_of_not_ge hBad
      obtain ⟨t,htL,htH⟩ := exists_between (max_lt hOrder hRoot)
      have hValue := (positive_iff a hp t).mp (hOpen t ⟨(le_max_left _ _).trans_lt htL,htH⟩)
      exact (not_lt_of_ge hValue) ((le_max_right _ _).trans_lt htL)
    exact ⟨(positive_iff a hp lo).mpr (hOrder.le.trans hc),(positive_iff a hp hi).mpr hc⟩

theorem zero_on_open (a : Affine) (lo hi : ℚ) (hOrder : lo<hi)
    (hOpen : ∀ t,lo<t ∧ t<hi → a.value t=0) : a.intercept=0 ∧ a.slope=0 := by
  let u := (2*lo+hi)/3
  let v := (lo+2*hi)/3
  have hu : lo<u ∧ u<hi := by dsimp only [u]; constructor <;> linarith only [hOrder]
  have hv : lo<v ∧ v<hi := by dsimp only [v]; constructor <;> linarith only [hOrder]
  have hUV : u<v := by dsimp only [u,v]; linarith only [hOrder]
  have hU := hOpen u hu
  have hV := hOpen v hv
  have hd : a.slope*(v-u)=0 := by unfold Affine.value at hU hV; nlinarith only [hU,hV]
  have hSlope : a.slope=0 := (mul_eq_zero.mp hd).resolve_right (sub_ne_zero.mpr hUV.ne')
  exact ⟨by simpa only [Affine.value,hSlope,zero_mul,add_zero] using hU,hSlope⟩

theorem equal_everywhere (a b : Affine) (lo hi : ℚ) (hOrder : lo<hi)
    (hOpen : ∀ t,lo<t ∧ t<hi → a.value t=b.value t) (t : ℚ) : a.value t=b.value t := by
  have hh := zero_on_open (difference a b) lo hi hOrder (fun t ht => by rw [difference_value,hOpen t ht,sub_self])
  have hz : (difference a b).value t=0 := by simp only [Affine.value,hh.1,hh.2,zero_mul,add_zero]
  rw [difference_value] at hz
  exact sub_eq_zero.mp hz

end Blotto.GeneralPaperRayClosedAffine
