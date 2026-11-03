import Blotto.GeneralPaperCodeLocation

/-! Increasing valid literal codes have increasing exact resource tags.
Grid-to-interior transitions use strict threshold increase; comparisons
within either pair use closed-before-open. Interior equality is derived
from the actual Farey separation lemma, not supplied by the catalogue.
-/
namespace Blotto.GeneralPaperCodeOrder
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperBucketGeometry
open GeneralPaperCodeLocation
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem flag_order (a : Alphabet) (t s r : ℕ) (x y : Choice)
    (hx : At a t s x) (hy : At a t r y) (hSlot : s≤r) (hPair : s<2 ↔ r<2) :
    x.opened=false ∨ y.opened=true := by
  have hs := hx.1
  have hr := hy.1
  have hEither : ¬(s=1 ∨ s=3) ∨ (r=1 ∨ r=3) := by omega
  rcases hEither with hClosed|hOpen
  · left
    simpa only [hClosed,decide_false] using hx.2.2.2
  · right
    simpa only [hOpen,decide_true] using hy.2.2.2

theorem same_bucket (a : Alphabet) (t s r : ℕ) (x y : Choice)
    (hx : At a t s x) (hy : At a t r y) (hSlot : s≤r) : x.tag≤y.tag := by
  apply (GeneralPaperResponseTag.le_iff _ _).mpr
  change x.threshold.value<y.threshold.value ∨
    (x.threshold.value=y.threshold.value ∧ (x.opened=false ∨ y.opened=true))
  by_cases hs : s<2
  · by_cases hr : r<2
    · exact Or.inr ⟨(hx.2.1 hs).trans (hy.2.1 hr).symm,
        flag_order a t s r x y hx hy hSlot (by omega)⟩
    · obtain ⟨f,_,hInside,hValue⟩ := hy.2.2.1 (by omega)
      exact Or.inl (by rw [hx.2.1 hs,hValue]; exact hInside.1)
  · have hr : 2≤r := by omega
    obtain ⟨f,hF,hInsideF,hValueF⟩ := hx.2.2.1 (by omega)
    obtain ⟨g,hG,hInsideG,hValueG⟩ := hy.2.2.1 hr
    have he := interiors_equal a.D a.C t a.orderPositive a.separated f g hF hG hInsideF hInsideG
    exact Or.inr ⟨hValueF.trans (he.trans hValueG.symm),flag_order a t s r x y hx hy hSlot (by omega)⟩

theorem decode_monotone (a : Alphabet) (responseX responseY : Bool) (c d : ℕ) (x y : Choice)
    (hX : (decode a responseX c).choice=some x) (hY : (decode a responseY d).choice=some y)
    (hCode : c≤d) : x.tag≤y.tag := by
  obtain ⟨t,s,hC,hx⟩ := decode_location a responseX c x hX
  obtain ⟨u,r,hD,hy⟩ := decode_location a responseY d y hY
  have hs := hx.1
  have hr := hy.1
  have hBuckets : t≤u := by omega
  rcases lt_or_eq_of_le hBuckets with hLt|hEq
  · apply (GeneralPaperResponseTag.le_iff _ _).mpr
    exact Or.inl (different_buckets a t u s r x y hx hy hLt)
  · subst u
    exact same_bucket a t s r x y hx hy (by omega)

theorem decoded_threshold_nonnegative (a : Alphabet) (response : Bool) (code : ℕ) (choice : Choice)
    (hSome : (decode a response code).choice=some choice) : 0≤choice.threshold.value := by
  obtain ⟨t,slot,_,hAt⟩ := decode_location a response code choice hSome
  exact (by unfold lower; positivity : 0≤lower a.C t).trans (value_lower a t slot choice hAt)

theorem decoded_threshold_le_one (a : Alphabet) (response : Bool) (code : ℕ) (choice : Choice)
    (hSome : (decode a response code).choice=some choice) : choice.threshold.value≤1 := by
  have hCap := valid_code_bound a response code (GeneralPaperCodeDecodeSound.decode_valid a response code choice hSome)
  have he := decode_monotone a response response code (4*a.C) choice ⟨grid a a.C,false⟩ hSome
    (GeneralPaperCodeDecodeSound.decode_one a response) hCap
  rcases (GeneralPaperResponseTag.le_iff _ _).mp he with hLt|⟨hEq,_⟩
  · change choice.threshold.value<(grid a a.C).value at hLt
    rw [grid_one] at hLt
    exact hLt.le
  · change choice.threshold.value=(grid a a.C).value at hEq
    rw [grid_one] at hEq
    exact hEq.le

end Blotto.GeneralPaperCodeOrder
