import Blotto.GeneralPaperLeastValidCell

/-! Literal code meanings locate each decoded threshold at its grid point
or at the unique bounded-denominator strict interior. These proof witnesses
do not run a division, floor, or Farey enumeration.
-/
namespace Blotto.GeneralPaperCodeLocation
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperBucketGeometry
set_option autoImplicit false
set_option maxHeartbeats 2500000

def At (a : Alphabet) (t slot : ℕ) (choice : Choice) : Prop :=
  slot<4 ∧
  (slot<2 → choice.threshold.value=lower a.C t) ∧
  (2≤slot → ∃ f : Farey.Fraction, f.den≤a.D ∧ Interior a.C t f.value ∧ choice.threshold.value=f.value) ∧
  choice.opened=decide (slot=1 ∨ slot=3)

theorem meaning_location (a : Alphabet) (response : Bool) (code : ℕ) (choice : Choice)
    (hMeaning : Denotes a response code choice.threshold.value choice.opened) :
    ∃ t slot, code=4*t+slot ∧ At a t slot choice := by
  rcases hMeaning with ⟨t,_,hCode,hValue,hOpen⟩|⟨_,t,_,hCode,hValue,hOpen⟩|
    ⟨t,f,_,hDen,hInside,hCode,hValue,hOpen⟩|⟨_,t,f,_,hDen,hInside,hCode,hValue,hOpen⟩
  · refine ⟨t,0,by simpa only [Nat.add_zero] using hCode,by decide,fun _ => hValue,by omega,?_⟩
    exact hOpen
  · refine ⟨t,1,hCode,by decide,fun _ => hValue,by omega,?_⟩
    exact hOpen
  · exact ⟨t,2,hCode,by decide,by omega,fun _ => ⟨f,hDen,hInside,hValue⟩,hOpen⟩
  · exact ⟨t,3,hCode,by decide,by omega,fun _ => ⟨f,hDen,hInside,hValue⟩,hOpen⟩

theorem decode_location (a : Alphabet) (response : Bool) (code : ℕ) (choice : Choice)
    (hSome : (decode a response code).choice=some choice) :
    ∃ t slot, code=4*t+slot ∧ At a t slot choice :=
  meaning_location a response code choice (GeneralPaperCodeDecodeSound.decode_sound a response code choice hSome).1

theorem value_lower (a : Alphabet) (t slot : ℕ) (choice : Choice) (hAt : At a t slot choice) :
    lower a.C t≤choice.threshold.value := by
  by_cases hs : slot<2
  · rw [hAt.2.1 hs]
  · obtain ⟨f,_,hInterior,hValue⟩ := hAt.2.2.1 (by omega)
    rw [hValue]
    exact hInterior.1.le

theorem value_upper (a : Alphabet) (t slot : ℕ) (choice : Choice) (hAt : At a t slot choice) :
    choice.threshold.value<upper a.C t := by
  by_cases hs : slot<2
  · rw [hAt.2.1 hs]
    have hc : (0:ℚ)<a.C := by exact_mod_cast a.scalePositive
    unfold lower upper
    exact (div_lt_div_iff_of_pos_right hc).mpr (by linarith)
  · obtain ⟨f,_,hInterior,hValue⟩ := hAt.2.2.1 (by omega)
    rw [hValue]
    exact hInterior.2

theorem next_grid_le (a : Alphabet) (t u : ℕ) (h : t<u) : upper a.C t≤lower a.C u := by
  have he : ((t:ℚ)+1)≤u := by exact_mod_cast h
  exact div_le_div_of_nonneg_right he (by exact_mod_cast a.scalePositive.le)

theorem different_buckets (a : Alphabet) (t u s r : ℕ) (x y : Choice)
    (hx : At a t s x) (hy : At a u r y) (hBucket : t<u) : x.threshold.value<y.threshold.value :=
  (value_upper a t s x hx).trans_le ((next_grid_le a t u hBucket).trans (value_lower a u r y hy))

end Blotto.GeneralPaperCodeLocation
