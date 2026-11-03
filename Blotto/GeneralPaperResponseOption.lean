import Blotto.GeneralPaperClosedAlphabet

/-! Every nonnegative real bid at most one has an actual decoded response
option at its greatest affordable closed threshold. Strictly larger bids
use the immediate open code; equality uses the closed code, including zero.
This finite selection is a proof observer, not an algorithmic enumeration.
-/
namespace Blotto.GeneralPaperResponseOption
open scoped Classical
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperClosedAlphabet
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem closed_response_meaning (a : Alphabet) (code : ℕ) (v : ℚ) (h : Denotes a false code v false) : Denotes a true code v false := by
  rcases h with ⟨t,ht,hc,hv,hf⟩|⟨h,_⟩|⟨t,f,ht,hd,hi,hc,hv,hf⟩|⟨h,_⟩
  · exact Or.inl ⟨t,ht,hc,hv,hf⟩
  · cases h
  · exact Or.inr (Or.inr (Or.inl ⟨t,f,ht,hd,hi,hc,hv,hf⟩))
  · cases h

theorem option_exists (a : Alphabet) (y : ℝ) (hy : 0≤y) (hOne : y≤1) :
    ∃ code choice, (decode a true code).choice=some choice ∧ choice.threshold.value=value a (lower a y hy) ∧
      choice.opened=decide ((value a (lower a y hy):ℝ)<y) := by
  let i := lower a y hy
  have hm : Denotes a false i.val.val (value a i) false := by
    have he := (GeneralPaperCodeDecodeSound.decode_sound a false i.val.val (choice a i) (decoded a i)).1
    rw [closed a i] at he
    exact he
  by_cases hs : (value a i:ℝ)<y
  · have hLess : value a i<1 := by exact_mod_cast hs.trans_le hOne
    obtain ⟨selected,hd,hv,hf⟩ := GeneralPaperCodeDecodeComplete.denotes_complete a true (i.val.val+1) (value a i) true
      (GeneralPaperCodeCoverage.closed_to_open a i.val.val (value a i) hm hLess)
    have hs' : (value a (lower a y hy):ℝ)<y := hs
    exact ⟨i.val.val+1,selected,hd,hv,by simpa only [hs',decide_true] using hf⟩
  · obtain ⟨selected,hd,hv,hf⟩ := GeneralPaperCodeDecodeComplete.denotes_complete a true i.val.val (value a i) false
      (closed_response_meaning a i.val.val (value a i) hm)
    have hs' : ¬(value a (lower a y hy):ℝ)<y := hs
    exact ⟨i.val.val,selected,hd,hv,by simpa only [hs',decide_false] using hf⟩

structure ResponseOption (a : Alphabet) (y : ℝ) (hy : 0≤y) where
  code : ℕ
  selected : Choice
  decoded : (decode a true code).choice=some selected
  threshold_value : selected.threshold.value=value a (lower a y hy)
  flag : selected.opened=decide ((value a (lower a y hy):ℝ)<y)

noncomputable def option (a : Alphabet) (y : ℝ) (hy : 0≤y) (hOne : y≤1) : ResponseOption a y hy :=
  let code := Classical.choose (option_exists a y hy hOne)
  let selected := Classical.choose (Classical.choose_spec (option_exists a y hy hOne))
  let spec := Classical.choose_spec (Classical.choose_spec (option_exists a y hy hOne))
  ⟨code,selected,spec.1,spec.2.1,spec.2.2⟩

theorem code_bound (a : Alphabet) (y : ℝ) (hy : 0≤y) (hOne : y≤1) : (option a y hy hOne).code<2^a.lambda := by
  rw [← a.dyadic]
  exact valid_in_alphabet a true _ (GeneralPaperCodeDecodeSound.decode_valid a true _ _ (option a y hy hOne).decoded)

theorem below (a : Alphabet) (y : ℝ) (hy : 0≤y) (hOne : y≤1) : ((option a y hy hOne).selected.threshold.value:ℝ)≤y := by
  rw [(option a y hy hOne).threshold_value]
  exact lower_le a y hy

theorem opened_strict (a : Alphabet) (y : ℝ) (hy : 0≤y) (hOne : y≤1) (hOpen : (option a y hy hOne).selected.opened=true) :
    ((option a y hy hOne).selected.threshold.value:ℝ)<y := by
  rw [(option a y hy hOne).flag,decide_eq_true_eq] at hOpen
  rw [(option a y hy hOne).threshold_value]
  exact hOpen

theorem physical_formula (a : Alphabet) (y : ℝ) (hy : 0≤y) (hOne : y≤1) (delta : ℚ) :
    ((option a y hy hOne).selected.physical delta:ℝ)=
      (value a (lower a y hy):ℝ)+if (value a (lower a y hy):ℝ)=y then 0 else (delta:ℝ) := by
  by_cases he : (value a (lower a y hy):ℝ)=y
  · have hs : ¬(value a (lower a y hy):ℝ)<y := by rw [he]; exact lt_irrefl _
    simp [Choice.physical,(option a y hy hOne).flag,(option a y hy hOne).threshold_value,hs,he]
  · have hs : (value a (lower a y hy):ℝ)<y := lt_of_le_of_ne (lower_le a y hy) he
    simp [Choice.physical,(option a y hy hOne).flag,(option a y hy hOne).threshold_value,hs,he]

end Blotto.GeneralPaperResponseOption
