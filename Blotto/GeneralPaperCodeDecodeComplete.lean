import Blotto.GeneralPaperCodeDecodeSound

/-! Every mathematical literal code meaning is produced by the actual
decoder, with the stipulated threshold value and open flag. The interior
cases use the complete executed midpoint query, without a supplied witness
or lookup oracle. Fraction labels may differ while representing one value.
-/
namespace Blotto.GeneralPaperCodeDecodeComplete
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCodeDecodeSound
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem denotes_complete (a : Alphabet) (response : Bool) (code : ℕ) (value : ℚ) (opened : Bool)
    (hMeaning : Denotes a response code value opened) :
    ∃ choice, (decode a response code).choice=some choice ∧ choice.threshold.value=value ∧ choice.opened=opened := by
  rcases hMeaning with ⟨t,ht,rfl,hValue,hOpen⟩|⟨hResponse,t,ht,rfl,hValue,hOpen⟩|
    ⟨t,f,ht,hDen,hInside,rfl,hValue,hOpen⟩|⟨hResponse,t,f,ht,hDen,hInside,rfl,hValue,hOpen⟩
  · exact ⟨⟨grid a t,false⟩,decode_grid a response t ht,hValue.symm,hOpen.symm⟩
  · subst response
    exact ⟨⟨grid a t,true⟩,decode_grid_open a t ht,hValue.symm,hOpen.symm⟩
  · obtain ⟨g,hLookup,hG⟩ := GeneralPaperMidpointComplete.lookup_complete a.D a.C t a.lambda
      a.orderPositive a.scalePositive ht a.separated a.dyadic f hDen hInside
    refine ⟨⟨g,false⟩,?_,hG.trans hValue.symm,hOpen.symm⟩
    rw [decode_at a response t 2 (by decide) (by omega),at_interior a response t ht,hLookup]
    rfl
  · subst response
    obtain ⟨g,hLookup,hG⟩ := GeneralPaperMidpointComplete.lookup_complete a.D a.C t a.lambda
      a.orderPositive a.scalePositive ht a.separated a.dyadic f hDen hInside
    refine ⟨⟨g,true⟩,?_,hG.trans hValue.symm,hOpen.symm⟩
    rw [decode_at a true t 3 (by decide) (by omega),at_interior_open a t ht,hLookup]
    rfl

theorem valid_iff_decode (a : Alphabet) (response : Bool) (code : ℕ) :
    Valid a response code ↔ ∃ choice, (decode a response code).choice=some choice := by
  constructor
  · rintro ⟨value,opened,hMeaning⟩
    obtain ⟨choice,hSome,_,_⟩ := denotes_complete a response code value opened hMeaning
    exact ⟨choice,hSome⟩
  · rintro ⟨choice,hSome⟩
    exact decode_valid a response code choice hSome

theorem denotes_unique (a : Alphabet) (response : Bool) (code : ℕ) (v w : ℚ) (p q : Bool)
    (hV : Denotes a response code v p) (hW : Denotes a response code w q) : v=w ∧ p=q := by
  obtain ⟨x,hx,hxv,hxp⟩ := denotes_complete a response code v p hV
  obtain ⟨y,hy,hyw,hyq⟩ := denotes_complete a response code w q hW
  have he : x=y := Option.some.inj (hx.symm.trans hy)
  subst y
  exact ⟨hxv.symm.trans hyw,hxp.symm.trans hyq⟩

end Blotto.GeneralPaperCodeDecodeComplete
