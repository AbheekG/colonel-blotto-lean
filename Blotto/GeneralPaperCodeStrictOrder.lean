import Blotto.GeneralPaperCodeOrder

/-! Distinct valid codes strictly order resource tags, including the two
closed/open pairs. Thus repeated fraction representations cannot create
two equal-tag literal codes. Threshold equality is always value equality.
-/
namespace Blotto.GeneralPaperCodeStrictOrder
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperBucketGeometry
open GeneralPaperCodeLocation
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem tag_lt_iff (x y : Choice) : x.tag<y.tag ↔ x.threshold.value<y.threshold.value ∨
    (x.threshold.value=y.threshold.value ∧ x.opened=false ∧ y.opened=true) := by
  constructor
  · intro hLt
    rcases (GeneralPaperResponseTag.le_iff _ _).mp hLt.le with hValue|⟨hValue,_⟩
    · exact Or.inl hValue
    · have hNot : ¬(y.opened=false ∨ x.opened=true) := by
        intro hFlag
        exact (not_le_of_gt hLt) ((GeneralPaperResponseTag.le_iff _ _).mpr (Or.inr ⟨hValue.symm,hFlag⟩))
      right
      refine ⟨hValue,?_,?_⟩
      · cases he : x.opened with
        | false => rfl
        | true => exact (hNot (Or.inr he)).elim
      · cases he : y.opened with
        | false => exact (hNot (Or.inl he)).elim
        | true => rfl
  · rintro (hValue|⟨hValue,hX,hY⟩)
    · apply lt_of_le_not_ge ((GeneralPaperResponseTag.le_iff _ _).mpr (Or.inl hValue))
      intro hReverse
      rcases (GeneralPaperResponseTag.le_iff _ _).mp hReverse with hR|⟨hR,_⟩ <;>
        dsimp only [Choice.tag] at hR <;> linarith
    · apply lt_of_le_not_ge ((GeneralPaperResponseTag.le_iff _ _).mpr (Or.inr ⟨hValue,Or.inl hX⟩))
      intro hReverse
      rcases (GeneralPaperResponseTag.le_iff _ _).mp hReverse with hR|⟨hR,hFlag⟩
      · change y.threshold.value<x.threshold.value at hR
        linarith
      · change y.opened=false ∨ x.opened=true at hFlag
        simp only [hX,hY,Bool.true_eq_false,Bool.false_eq_true,or_self] at hFlag

theorem same_bucket (a : Alphabet) (t s r : ℕ) (x y : Choice)
    (hx : At a t s x) (hy : At a t r y) (hSlot : s<r) : x.tag<y.tag := by
  apply (tag_lt_iff x y).mpr
  have hsBound := hx.1
  have hrBound := hy.1
  by_cases hs : s<2
  · by_cases hr : r<2
    · have hs0 : s=0 := by omega
      have hr1 : r=1 := by omega
      subst s
      subst r
      exact Or.inr ⟨(hx.2.1 (by decide)).trans (hy.2.1 (by decide)).symm,hx.2.2.2,hy.2.2.2⟩
    · obtain ⟨f,_,hInside,hValue⟩ := hy.2.2.1 (by omega)
      exact Or.inl (by rw [hx.2.1 hs,hValue]; exact hInside.1)
  · have hs2 : s=2 := by omega
    have hr3 : r=3 := by omega
    subst s
    subst r
    obtain ⟨f,hF,hInsideF,hValueF⟩ := hx.2.2.1 (by decide)
    obtain ⟨g,hG,hInsideG,hValueG⟩ := hy.2.2.1 (by decide)
    have he := interiors_equal a.D a.C t a.orderPositive a.separated f g hF hG hInsideF hInsideG
    exact Or.inr ⟨hValueF.trans (he.trans hValueG.symm),hx.2.2.2,hy.2.2.2⟩

theorem decode_strict (a : Alphabet) (responseX responseY : Bool) (c d : ℕ) (x y : Choice)
    (hX : (decode a responseX c).choice=some x) (hY : (decode a responseY d).choice=some y)
    (hCode : c<d) : x.tag<y.tag := by
  obtain ⟨t,s,hC,hx⟩ := decode_location a responseX c x hX
  obtain ⟨u,r,hD,hy⟩ := decode_location a responseY d y hY
  have hs := hx.1
  have hr := hy.1
  have hBuckets : t≤u := by omega
  rcases lt_or_eq_of_le hBuckets with hLt|hEq
  · exact (tag_lt_iff x y).mpr (Or.inl (different_buckets a t u s r x y hx hy hLt))
  · subst u
    exact same_bucket a t s r x y hx hy (by omega)

theorem code_eq_iff_tag_eq (a : Alphabet) (responseX responseY : Bool) (c d : ℕ) (x y : Choice)
    (hX : (decode a responseX c).choice=some x) (hY : (decode a responseY d).choice=some y) :
    c=d ↔ x.tag=y.tag := by
  constructor
  · intro he
    exact le_antisymm (GeneralPaperCodeOrder.decode_monotone a responseX responseY c d x y hX hY he.le)
      (GeneralPaperCodeOrder.decode_monotone a responseY responseX d c y x hY hX he.ge)
  · intro he
    rcases lt_trichotomy c d with hLt|hEq|hGt
    · have ht := decode_strict a responseX responseY c d x y hX hY hLt
      rw [he] at ht
      exact (lt_irrefl _ ht).elim
    · exact hEq
    · have ht := decode_strict a responseY responseX d c y x hY hX hGt
      rw [he] at ht
      exact (lt_irrefl _ ht).elim

end Blotto.GeneralPaperCodeStrictOrder
